-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
-- name    : QAlgorithms_Papers_Independent_Renew46_P43
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T06:13:58.913646+00:00
-- url     : https://prove2.me/theorems/613e6bb9-f9ee-4968-a860-6e5d0cb75480
-- title:
--   Definitions for Coding Theorems of Quantum Information Theory
-- statement:
--   The objects the formalized statements of *Coding Theorems of Quantum Information Theory* (arXiv:quant-ph/9907077) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `wordTensor`: PDF pp.8,11: product of a list of matrices, with time in increasing coordinate order.
--   - `exp2`: PDF p.11: base-two exponential.
--   - `pmfEntropy`: PDF p.11: Shannon entropy, with the continuous zero-mass convention.
--   - `varianceSet`: PDF p.11: variance-typical sequences, including the zero-probability constraints.
--   - `varianceConstant`: PDF p.12: K_V = 2 log_2(e)/e, distinct from the entropy-variance constant.
--   - `FineResolution`: PDF pp.12-14: a chosen fine spectral resolution, including zero eigenvalues and a full choice of rank-one projectors inside degenerate eigenspaces.
--   - `FineResolution.law`: PDF p.12: the normalized spectral weights, adapted to the PMF interface.
--   - `FineResolution.atom`: PDF pp.12-14: fine projections computed from columns of the accepted unitary basis. Column phases cancel; all degeneracy choices remain available.
--   - `FineResolution.state`: PDF p.12: the state constructed from its spectral resolution.
--   - `varianceProjector`: PDF p.12: variance-typical projector in the chosen spectral basis.
--   - `spectralN`: PDF p.12: rank of sqrt(rho(1-rho)), evaluated on its spectral list.
--   - `spectralMu`: PDF p.12: least positive eigenvalue of sqrt(rho(1-rho)); zero on empty support.
--   - `varianceTail`: PDF p.12: the explicitly natural-exponential variance tail; pure states have N=0.
--   - `IsShadow`: PDF p.12: an eta-shadow is an effect with at least eta state mass.
--   - `entropyProjector`: PDF pp.13-14: entropy-typical projector. Zero-probability spectral words are excluded rather than assigning them the totalized value log(0).
--   - `entropyConstant`: PDF p.14: choose the advertised upper bound as the common K_H(d). Increasing a valid variance constant only decreases all stated lower bounds.
--   - `constantProjector`: PDF p.14: constant-typical projector, with absolute coordinate deviations.
--   - `complexOperatorNorm`: PDF p.15: the operator norm, expressed using the induced Euclidean operator.
--   - `etaFunction`: PDF pp.15,64: eta(t)=-t log_2(t), including eta(0)=0.
--   - `IsCountablePOVM`: PDF pp.10,62: a genuinely countable POVM; HasSum rules out a junk tsum.
--   - `sqrtInstrumentBranch`: PDF p.10: square-root instrument branch.
--   - `interior`: PDF p.10: the actual nonselective operation, including every outcome.
--   - `totalDisturbance`: PDF p.10: trace norm of the labelled block-diagonal difference. For countably many outcomes the one norm on the direct sum is the sum of the block one norms.
--   - `PureSource`: PDF pp.7-8: a finite set of distinct pure letters with an arbitrary probability law.
--   - `PureSource.average`: PDF p.7: average source state, computed from the ensemble.
--   - `PureSource.weight`: PDF pp.7-8: iid word probability.
--   - `PureSource.word`: PDF pp.7-8: the actual pure product word.
--   - `SourceCode`: PDF p.7: arbitrary state-valued encoding and a CPTP decoder. The resource is Hilbert dimension k, with no restriction on the decoder's Kraus rank or isometry.
--   - `SourceCode.fidelity`: PDF p.7: average overlap fidelity of the actual code.
--   - `SourceCode.distortion`: PDF p.8: average half-trace-norm distortion.
--   - `SourceCode.rate`: PDF p.11: log_2(dim K)/n, guarded by the code's positive dimension and length.
--   - `EncoderExtension`: PDF pp.7-8: a quantum encoding extends the given state-valued encoder by one fixed CPTP map on every matrix, including off-diagonal operators.
--   - `purification`: PDF p.8: a specific purification with reference first, obtained by vectorizing sqrt(rho); its partial trace over the reference is rho for every density operator.
--   - `sourceFe`: PDF p.8: source-state entanglement fidelity, using the actual extended channel.
--   - `SourceQuality`: PDF pp.11,19: the four operational code qualities used in Chapter I.
--   - `MeetsQuality`: PDF pp.11,19: quality of an actual block code. No quantum extension is assumed for arbitrary encoding, and entanglement fidelity is only evaluated on a CPTP extension.
--   - `minimumSourceRate`: PDF p.11: minimum rate among actual codes; the extended nonnegative real infimum is +infinity on an empty feasible set, never a spurious zero.
--   - `sourceRate`: PDF p.11: fixed-error operational limsup of block minima; n+1 ranges exactly over all positive lengths.
--   - `projectionEncoder`: PDF p.16: the actual compression map into the range coordinates of an isometry V. For a state the second coefficient is (1-Tr(rho Pi))/k.
--   - `IntrinsicSystem`: PDF pp.60-61: a finite C*-algebra in a multiplicity-free direct-sum representation. Its ordinary matrix trace is intrinsic; dim is the SUM of block Hilbert dimensions.
--   - `IntrinsicSystem.IsState`: PDF p.61: intrinsic normalized states, including classical and hybrid systems.
--   - `IntrinsicSystem.IsPureState`: PDF p.61: minimal intrinsic projections, represented by rank-one block states.
--   - `intrinsicAmplification`: PDF p.62: matrix amplification of a Heisenberg map, preserving the ancillary matrix blocks, not just diagonal ancillary states.
--   - `IntrinsicOperation`: PDF p.62: a CP-unital Heisenberg map on the specified block algebras. Its linear extension off the domain algebra is immaterial and is not assumed positive.
--   - `Embedding`: PDF pp.61,65: a subsystem inclusion, in independent intrinsic coordinates. No tensor-factor representation or disjointness is imposed.
--   - `Hom`: PDF p.66: a star homomorphism, which is not required injective.
--   - `CommutingImages`: PDF pp.62,65: elementwise compatibility of two map images.
--   - `intrinsicRestriction`: PDF pp.62,65-69: the intrinsic trace adjoint, using only matrix units that belong to the domain algebra. This is restriction for an inclusion map.
--   - `viewedEntropy`: PDF p.69: H(phi)=H(phi_*rho), for the one fixed ambient state rho.
--   - `jointState`: PDF pp.66,69: the state pulled back by the product map F G. Compatibility makes this a joint state; central overlaps are allowed.
--   - `intrinsicMutualInformation`: PDF pp.65,69: mutual information, formed from the same ambient rho throughout.
--   - `intrinsicConditionalEntropy`: PDF pp.65,69: conditional entropy; it may be negative.
--   - `familyState`: PDF pp.62,68: joint pullback for any finite family. Product order is fixed by the finite list; theorems require distinct images to commute, so the choice is irrelevant.
--   - `familyEntropy`: PDF pp.65,68: entropy of the generated algebra of a subset of a compatible family, computed by the trace adjoint of multiplication, which preserves its intrinsic spectrum.
--   - `Diagonalization`: PDF pp.66-67: positive-coefficient diagonalization of a state, on its support; zero eigenspaces are not required in this definition.
--   - `TraceNonincreasing`: PDF p.70: the source's maximality condition, on positive domain elements.
--   - `classicalKLTerm`: PDF pp.64-65: nonnegative base-two relative-entropy contribution. The continuous zero-first-mass value is q / log 2, so the linear corrections sum to zero for normalized laws, including laws with zero entries. This form avoids undefined infinity-minus-infinity for countably many outcomes.
--   - `countableEntropy`: PDF pp.62,65: entropy of a countable probability law, possibly +infinity.
--   - `measuredInformation`: PDF p.72: the actual outcome-law mutual information of commuting observables.
--   - `hybridInformation`: PDF pp.70,72: mutual information between an intrinsic subsystem and a countable observable, as the weighted divergence of its posterior states from its marginal.
--   - `cqAverage`: PDF p.73: average state for an arbitrary measurable input law.
--   - `cqInformation`: PDF p.73: cq mutual information, defined by relative entropy before invoking the entropy-difference identity, including arbitrary input probability measures.
--   - `cqMeasuredInformation`: PDF pp.37,73: measured information from the conditional and marginal outcome laws of the actual POVM, including countably many outcomes.
--   - `fullAlgebra`: PDF pp.60-61: a full matrix system in intrinsic coordinates.
--   - `identityOperation`: PDF pp.61,65: the identity is a CP-unital operation on every intrinsic system.
--   - `identityEmbedding`: PDF p.65: identity subsystem, used for sanity checks of restriction.
--   - `xIndices`: PDF p.74: two copies of the finite factor index, labelled as X and Y.
--   - `yIndices`: PDF p.74: the Y labels, separate from the X labels.
--   - `observableJoint`: PDF pp.69-70: joint state of a finite observable and a compatible intrinsic subsystem, with the observable's actual outcome retained.
--   - `HybridSource`: PDF pp.53-55: a possibly correlated finite classical/hybrid pure-letter source. The law is joint on all classical letters and the pure Y letter; it need not factor.
--   - `HybridSource.marginal`: PDF pp.53,57: the computed marginal state on X(J)Y of the joint source law.
--   - `HybridSource.subsetEntropy`: PDF pp.57-58: H(X(J)|YX(J^c)), computed from the same correlated source.
--   - `HybridSource.lowerRegion`: PDF pp.57-58: upward unbounded source rate region, with lower subset constraints.
--   - `HybridSource.corner`: PDF p.58: source permutation corner, conditioned on the preceding classical letters and Y, with the source's order rather than its reverse.
--   - `IsExtreme`: PDF p.57: ordinary extremality; no coordinatewise upper-maximality condition.
--   - `empiricalWeight`: PDF p.29: empirical law weights; the source calls this the type of the word. Positive n is required in every theorem using this definition.
--   - `wordConditionalEntropy`: PDF p.29: conditional output entropy for the actual word's empirical law.
--   - `conditionalVarianceProjector`: PDF p.29: conditional variance-typical projector. Equal input letters are grouped in the count conditions; the tensor factors remain in their original time order. An empty input-letter group imposes only 0≤0 and contributes the scalar identity.
--   - `changeSpectrum`: PDF pp.30-31: change the eigenvalue list in a chosen simultaneous fine basis.
--   - `divergenceTail`: PDF p.31: base-two divergence tail, with 2^{-n*infinity}=0 at positive n.
--   - `PartyWords`: PDF pp.45-46: the regrouped multi-party basis, with each sender holding a word.
--   - `MultipleData`: PDF p.45: finite pure-letter source data. Validity is stated separately so that explicit example ensembles can be constructed without admitted definition proofs.
--   - `MultipleData.Valid`: PDF p.45: source validity, with no product-state promise or independent sender law.
--   - `MultipleData.average`: PDF p.45: computed average source density.
--   - `MultipleData.word`: PDF pp.45-46: the actual temporal word, regrouped by sender.
--   - `MultipleData.blockAverage`: PDF p.46: the average block state, in the same party grouping as the encoder.
--   - `multipleMarginal`: PDF p.45: partial trace to any sender subset, including the empty subset.
--   - `partyMaps`: PDF p.45: tensor product of heterogeneous local maps, on all matrix units. This preserves entangled source letters and does not replace them by their marginals.
--   - `MultipleCode`: PDF pp.45-46: joint CPTP decoder with range in the actual product block algebra. CPTP extensions from intrinsic input algebras to full matrices are equivalent by precomposing block pinching. This imposes no restriction on intrinsic local encoders.
--   - `MultipleCode.channel`: PDF p.46: the full joint source recovery channel.
--   - `MultipleCode.rate`: PDF p.46: rate of each actual local compression space.
--   - `MultipleCode.fidelity`: PDF p.46: ensemble-averaged pure-word fidelity.
--   - `MultipleCode.distortion`: PDF p.46: ensemble-averaged half trace distance.
--   - `quantumSourceRegion`: PDF p.46: actual code-sequence rate region; error vanishes and every rate coordinate converges to the specified rate, over all positive lengths.
--   - `entanglementSourceRegion`: PDF p.46: Fe only for fully quantum systems. The explicit domain guard prevents an assertion of a purification rate region on a hybrid system.
--   - `HybridSource.systems`: PDF pp.53-55: intrinsic systems, with Y the last party.
--   - `HybridSource.classicalCoordinate`: Read a classical coordinate through the fixed dependent-system identification.
--   - `HybridSource.quantumCoordinate`: Read Y through the same fixed dependent-system identification.
--   - `HybridSource.multiple`: PDF pp.53-55: the actual joint classical/pure-Y source, with Y the last party.
--   - `HybridSource.withYRate`: PDF pp.55-56: append the entropy of Y to the classical compression rates.
--   - `ProductData`: PDF pp.45-46: product-letter data for arbitrary local encoders. The JOINT law may be correlated; only each source letter is a product across senders.
--   - `ProductData.Valid`: PDF pp.45-46: normalized distinct local pure letters in the respective intrinsic systems.
--   - `ProductData.multiple`: PDF p.45: construct the joint pure ensemble from local product letters and the original correlated law, rather than replacing that law by a product of marginals.
--   - `ArbitraryMultipleCode`: PDF p.46: arbitrary separate state-valued encoders and an actual joint CPTP decoder. Only the local word is supplied to each encoder.
--   - `ArbitraryMultipleCode.fidelity`: PDF p.46: actual average overlap quality for the arbitrary local encoders.
--   - `ArbitraryMultipleCode.distortion`: PDF p.46: average half trace norm for the same arbitrary code.
--   - `arbitrarySourceRegion`: PDF p.46: arbitrary-encoding operational region, only on product-letter sources.
--   - `SourceRegionProperties`: PDF p.46: closed, convex and coordinatewise upward closed, including unbounded regions.
--   - `wheelVector`: PDF pp.47-48: the four wheel vectors |0>,|1>,|+>,|->, with real signs.
--   - `clonedWheel`: PDF pp.47-48: the actual cloned-wheel source, with the same randomly chosen pure state sent to both encoders. Its law is diagonal, not independent across parties.
--   - `clonedCross`: PDF p.52: the two orthogonal alternatives of the cloned cross.
--   - `eprSourceVector`: PDF pp.51-52: the two Bell alternatives |Phi+> and |Phi->, in party coordinates.
--   - `eprSource`: PDF p.51: the actual equidistributed EPR source.
--   - `wheelQuantumOuter`: PDF pp.47-48: the necessary quantum cloned-wheel rate region.
--   - `nonnegativeSumRegion`: PDF p.48: the arbitrary-encoding sum-rate region for a two-source example.
--   - `halfRateRegion`: PDF pp.51-52: the half-qubit individual-rate necessary constraints.
--   - `StateChannel`: PDF p.20: nonstationary channels are arbitrary nonempty measurable state sets on the one fixed output system. Input laws need not have finite support.
--   - `StateChannel.capacity`: PDF p.24: single-use capacity, optimized over all probability measures on the measurable state set. Information is bounded by log_2(dim A's Hilbert representation), so the real supremum is bounded and nonempty.
--   - `NonstationaryCode`: PDF pp.23-24: actual nonstationary product-state code with a collective block POVM and a failure outcome. The error criterion is maximum message error.
--   - `NonstationaryCode.error`: PDF p.23: maximum error, with the message-set nonemptiness enforced in the code.
--   - `nonstationaryN`: PDF p.23: optimal number of messages among actual codes. For 0≤lambda<1 the set is nonempty and bounded by dim(output)^n/(1-lambda), so Nat.sSup is an actual finite maximum; no statement below uses this definition in the unbounded lambda≥1 regime.
--   - `MaximalCodeConclusion`: PDF pp.24-25: all maximal-code conclusions, including membership in the large event and the trace bound for actual chosen entropy-typical projectors.
--   - `FiniteChannel`: PDF p.28: finite stationary channel, with input labels retained even when several labels are mapped to the same output state.
--   - `FiniteChannel.information`: PDF pp.28-29: finite-law Holevo information, using the same normalized channel.
--   - `FiniteChannel.capacity`: PDF p.28: capacity of the finite channel; PMF is compact and nonempty, and information is bounded. This real supremum has no empty/unbounded-set junk.
--   - `FiniteCode`: PDF pp.23,28: finite stationary code, collective decoding, optional failure.
--   - `FiniteCode.error`: PDF pp.23,28: maximum-message error for the actual channel and decoder.
--   - `finiteN`: PDF p.28: actual optimal message count, finite whenever lambda<1.
--   - `FiniteCode.Composition`: PDF pp.28,33: the code really has a fixed empirical composition P.
--   - `FiniteCode.codebook`: PDF p.53: actual finite codebook, with duplicate encodings removed as a set.
--   - `IntrinsicSourceCode`: PDF p.20: an intrinsic-output source code must decode into the declared block algebra. Quantum input maps may be extended by precomposing intrinsic block pinching.
--   - `intrinsicSourceRate`: PDF p.20: fixed-error rates in the intrinsic source algebra; resource cost is log Hilbert dimension of the compressed system, not dimension of the algebra.
--   - `letterOutputEntropy`: PDF pp.28,34: H(V|P), for any finite family of output states.
--   - `conditionalDivergence`: PDF pp.28,34: conditional quantum divergence, allowing unsupported output states and zero-probability input letters (0*infinity=0 in ENNReal).
--   - `individualExponent`: PDF p.34: individual entropy-threshold exponent, with empty infimum +infinity.
--   - `collectiveExponent`: PDF p.34: collective entropy-threshold exponent.
--   - `greedyExponent`: PDF p.34: E_g(R,P); the factor 1/2 multiplies ONLY the collective exponent. The supremum is paired with an explicit attainment conclusion below.
--   - `greedyBound`: PDF p.35: optimize the greedy bound over all rate-admissible input laws.
--   - `sphereExponent`: PDF p.35: sphere-packing exponent, minimizing over the full normalized channel class, with no commutativity restriction on comparison-channel states.
--   - `sphereBound`: PDF p.36: global sphere-packing bound. Attainment is stated below.
--   - `minimumChannelError`: PDF p.28: minimum maximum error among actual n-block codes at rate at least R.
--   - `errorExponent`: PDF p.34: a zero error has exponent +infinity, not totalized log(0)=0.
--   - `reliability`: PDF p.34: joint liminf in length tending to infinity and POSITIVE rate slack tending to zero. It is not the error exponent at the exactly fixed finite-block rate.
--   - `universalRange`: PDF p.17: least common support over ALL states and ALL fine bases of entropy at most R, not just the eigenbasis of the particular source being compressed.
--   - `universalProjector`: PDF p.17: the orthogonal projector onto the actual universal least common support.
--   - `highEntropyDivergence`: PDF p.17: entropy-constrained divergence infimum. An empty constraint set has value +infinity and therefore a zero exponential tail.
--   - `countTypes`: PDF p.31: finitely many realizable count vectors, with no uncountable sum.
--   - `exactProjector`: PDF pp.30-31: exact spectral-type projector for a prescribed count vector.
--   - `spectralTypeState`: PDF p.31: state of a realizable spectral type; positive length is required below.
--   - `highEntropyProjector`: PDF p.31: the entropy-high spectral projector is a finite sum of exact types.
--   - `conditionalTypes`: PDF p.31: realizable conditional count tables for a fixed input word.
--   - `conditionalExactProjector`: PDF p.31: the conditional exact-type projector, with original time order restored.
--   - `conditionalTypeState`: PDF p.31: a realizable conditional type's comparison states. An empty input class is assigned the original state; its entropy/divergence weight is exactly zero.
--   - `lowConditionalProjector`: PDF p.31: conditional entropy-low projector, as a finite sum of realizable types.
--   - `lowEntropyDivergence`: PDF p.31: low-entropy divergence infimum for a single normalized state.
--   - `SideCode`: PDF pp.53-55: separate classical encoders and a collective conditioned POVM on the free Y^n register, retaining an explicit failure outcome.
--   - `HybridSource.classicalWords`: PDF pp.53-55: classical words obtained from an iid joint source word.
--   - `HybridSource.sideWord`: PDF pp.53-55: Y word, with the correct block power.
--   - `SideCode.message`: PDF pp.53-55: actual message tuple, each message seeing its own classical word only.
--   - `SideCode.error`: PDF pp.53-55: ensemble-averaged whole-tuple decoding error.
--   - `SideCode.disturbance`: PDF pp.53-55: mean unhalved trace norm for the actual labelled square-root instrument after discarding transmitted classical messages, including its failure block.
--   - `SideCode.rate`: PDF pp.53-55: classical message rate in bits per source symbol.
--   - `HybridSource.classicalMass`: PDF p.54: marginal probability of a classical tuple.
--   - `HybridSource.conditional`: PDF p.54: conditional Y state. A zero-mass branch is filled by a fixed source pure state, rather than by an unnormalized zero state.
--   - `ClassicalSideCode`: PDF pp.56-57: quantum source encoder with classical side information. The `encoderKnows` flag changes its actual domain: false requires one common encoding for every classical word; the decoder always receives the classical word for free.
--   - `ClassicalSideCode.fidelity`: PDF pp.56-57: actual ensemble-averaged pure-word fidelity.
--   - `classicalSideRate`: PDF p.57: fixed-error limsup of operational minimum rates, with the encoder's side-information domain part of the code type.
--   - `independentLaw`: PDF pp.40,43: the independent sender law, constructed before the pure conditional-output refinement. The product normalization is a finite distributive law.
--   - `macReductionSource`: PDF p.43: source reduction data, with the source constructed from normalized pure decompositions of EVERY channel output and the independent sender laws.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, https://arxiv.org/abs/quant-ph/9907077v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

/-!
A. Winter, Coding Theorems of Quantum Information Theory, quant-ph/9907077v1.
All logarithms and unnamed exponentials are base two. Real.exp is used only for
explicit e-exponentials. Local definitions are confined to this paper.
Compilation is pending the independent mechanical batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator
open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open QAlgorithms.Papers.Independent.Information100.P06 (Below)
open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)
open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)
open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8,11: product of a list of matrices, with time in increasing coordinate order. -/
def wordTensor {n : ℕ} {I : Fin n → Type*}
    (rho : ∀ i, Matrix (I i) (I i) ℂ) : Matrix (∀ i, I i) (∀ i, I i) ℂ :=
  fun a b => ∏ i, rho i (a i) (b i)

/-- PDF p.11: base-two exponential. -/
def exp2 (x : ℝ) : ℝ := (2 : ℝ) ^ x

/-- PDF p.11: Shannon entropy, with the continuous zero-mass convention. -/
def pmfEntropy {I : Type} [Fintype I] (P : PMF I) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P27.shannon (fun i => (P i).toReal)

/-- PDF p.11: variance-typical sequences, including the zero-probability constraints. -/
def varianceSet {I : Type*} [Fintype I] [DecidableEq I] (P : PMF I)
    (n : ℕ) (alpha : ℝ) : Finset (Fin n → I) :=
  Finset.univ.filter fun w => ∀ i,
    |(count w i : ℝ) - n * (P i).toReal| ≤
      alpha * Real.sqrt ((P i).toReal * (1 - (P i).toReal)) * Real.sqrt n

/-- PDF p.12: K_V = 2 log_2(e)/e, distinct from the entropy-variance constant. -/
def varianceConstant : ℝ := 2 * Real.logb 2 (Real.exp 1) / Real.exp 1

/-- PDF pp.12-14: a chosen fine spectral resolution, including zero eigenvalues
and a full choice of rank-one projectors inside degenerate eigenspaces. -/
abbrev FineResolution (d : ℕ) :=
  QAlgorithms.Papers.Independent.Dependency50.P19.Spectrum (Fin d)

/-- PDF p.12: the normalized spectral weights, adapted to the PMF interface. -/
def FineResolution.law {d : ℕ} (S : FineResolution d) : PMF (Fin d) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (S.weight j)) (by
    calc
      ∑ j, ENNReal.ofReal (S.weight j) = ENNReal.ofReal (∑ j, S.weight j) :=
        (ENNReal.ofReal_sum_of_nonneg (fun j _ => S.nonneg j)).symm
      _ = 1 := by rw [S.total]; norm_num)

/-- PDF pp.12-14: fine projections computed from columns of the accepted unitary basis.
Column phases cancel; all degeneracy choices remain available. -/
def FineResolution.atom {d : ℕ} (S : FineResolution d) (j : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a b => (S.basis : Matrix (Fin d) (Fin d) ℂ) a j *
    conj ((S.basis : Matrix (Fin d) (Fin d) ℂ) b j)

/-- PDF p.12: the state constructed from its spectral resolution. -/
def FineResolution.state {d : ℕ} (S : FineResolution d) : Matrix (Fin d) (Fin d) ℂ :=
  QAlgorithms.Papers.Independent.Dependency50.P19.Spectrum.density S

/-- PDF p.12: variance-typical projector in the chosen spectral basis. -/
def varianceProjector {d : ℕ} (S : FineResolution d) (n : ℕ) (alpha : ℝ) :=
  ∑ w ∈ varianceSet S.law n alpha, wordTensor (fun k => S.atom (w k))

/-- PDF p.12: rank of sqrt(rho(1-rho)), evaluated on its spectral list. -/
def spectralN {d : ℕ} (S : FineResolution d) : ℕ :=
  (Finset.univ.filter fun j => 0 < Real.sqrt ((S.law j).toReal * (1 - (S.law j).toReal))).card

/-- PDF p.12: least positive eigenvalue of sqrt(rho(1-rho)); zero on empty support. -/
def spectralMu {d : ℕ} (S : FineResolution d) : ℝ :=
  let v := fun j => Real.sqrt ((S.law j).toReal * (1 - (S.law j).toReal))
  let support := Finset.univ.filter fun j => 0 < v j
  if h : support.Nonempty then support.inf' h v else 0

/-- PDF p.12: the explicitly natural-exponential variance tail; pure states have N=0. -/
def varianceTail {d : ℕ} (S : FineResolution d) (alpha : ℝ) : ℝ :=
  2 * spectralN S * Real.exp (-2 * (spectralMu S)^2 * alpha^2)

/-- PDF p.12: an eta-shadow is an effect with at least eta state mass. -/
def IsShadow {I : Type*} [Fintype I] [DecidableEq I]
    (rho B : Matrix I I ℂ) (eta : ℝ) : Prop := IsEffect B ∧ eta ≤ effectProb rho B

/-- PDF pp.13-14: entropy-typical projector. Zero-probability spectral words are
excluded rather than assigning them the totalized value log(0). -/
def entropyProjector {d n : ℕ} (S : Fin n → FineResolution d) (delta : ℝ) :=
  ∑ w ∈ (Finset.univ.filter fun w : Fin n → Fin d =>
    (∀ i, 0 < ((S i).law (w i)).toReal) ∧
    |(∑ i, -Real.logb 2 ((S i).law (w i)).toReal) -
      ∑ i, vnEntropy (S i).state| ≤ delta * Real.sqrt n),
    wordTensor (fun i => (S i).atom (w i))

/-- PDF p.14: choose the advertised upper bound as the common K_H(d).
Increasing a valid variance constant only decreases all stated lower bounds. -/
def entropyConstant (d : ℕ) : ℝ := max ((Real.logb 2 3)^2) ((Real.logb 2 d)^2)

/-- PDF p.14: constant-typical projector, with absolute coordinate deviations. -/
def constantProjector {d : ℕ} (S : FineResolution d) (n : ℕ) (delta : ℝ) :=
  ∑ w ∈ (Finset.univ.filter fun w : Fin n → Fin d => ∀ j,
    |(count w j : ℝ) - n * (S.law j).toReal| ≤ delta * Real.sqrt n),
    wordTensor (fun i => S.atom (w i))

/-- PDF p.15: the operator norm, expressed using the induced Euclidean operator. -/
def complexOperatorNorm {I : Type*} [Fintype I] (M : Matrix I I ℂ) : ℝ :=
  ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖

/-- PDF pp.15,64: eta(t)=-t log_2(t), including eta(0)=0. -/
def etaFunction (t : ℝ) : ℝ := -t * Real.logb 2 t

/-- PDF pp.10,62: a genuinely countable POVM; HasSum rules out a junk tsum. -/
def IsCountablePOVM {B I : Type*} [Countable B] [Fintype I] [DecidableEq I]
    (D : B → Matrix I I ℂ) : Prop :=
  (∀ b, (D b).PosSemidef) ∧ HasSum D 1

/-- PDF p.10: square-root instrument branch. -/
def sqrtInstrumentBranch {B I : Type*} [Fintype I] [DecidableEq I]
    (D : B → Matrix I I ℂ) (rho : Matrix I I ℂ) (b : B) :=
  cfc Real.sqrt (D b) * rho * cfc Real.sqrt (D b)

/-- PDF p.10: the actual nonselective operation, including every outcome. -/
def interior {B I : Type*} [Fintype I] [DecidableEq I]
    (D : B → Matrix I I ℂ) (rho : Matrix I I ℂ) := ∑' b, sqrtInstrumentBranch D rho b

/-- PDF p.10: trace norm of the labelled block-diagonal difference. For countably
many outcomes the one norm on the direct sum is the sum of the block one norms. -/
def totalDisturbance {B I : Type*} [Fintype I] [DecidableEq I]
    (D : B → Matrix I I ℂ) (rho : Matrix I I ℂ) (label : B) : ℝ :=
  ∑' b, traceNorm ((if b = label then rho else 0) - sqrtInstrumentBranch D rho b)

/-! Small definition checks, with no admitted proof. -/

example {I : Type*} (rho : Matrix I I ℂ) (a b : Fin 0 → I) : copies 0 rho a b = 1 := by
  simp [copies, Matrix.of_apply]

example {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    traceDistance rho rho = 0 := by simp [traceDistance, traceNorm, cfc_zero]

example : etaFunction 0 = 0 := by simp [etaFunction]

example {B I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) (b : B) :
    sqrtInstrumentBranch (fun _ : B => 0) rho b = 0 := by simp [sqrtInstrumentBranch, cfc_zero]

/-- PDF pp.7-8: a finite set of distinct pure letters with an arbitrary probability law. -/
structure PureSource (a d : ℕ) where
  alphabet_pos : 0 < a
  dimension_pos : 0 < d
  law : PMF (Fin a)
  letter : Fin a → Matrix (Fin d) (Fin d) ℂ
  pure : ∀ x, IsPure (letter x)
  distinct : Function.Injective letter

/-- PDF p.7: average source state, computed from the ensemble. -/
def PureSource.average {a d : ℕ} (S : PureSource a d) :=
  ∑ x, ((S.law x).toReal : ℂ) • S.letter x

/-- PDF pp.7-8: iid word probability. -/
def PureSource.weight {a d n : ℕ} (S : PureSource a d) (w : Fin n → Fin a) : ℝ :=
  ∏ i, (S.law (w i)).toReal

/-- PDF pp.7-8: the actual pure product word. -/
def PureSource.word {a d n : ℕ} (S : PureSource a d) (w : Fin n → Fin a) :=
  wordTensor (fun i => S.letter (w i))

/-- PDF p.7: arbitrary state-valued encoding and a CPTP decoder. The resource is
Hilbert dimension k, with no restriction on the decoder's Kraus rank or isometry. -/
structure SourceCode {a d : ℕ} (S : PureSource a d) (n : ℕ) where
  length_pos : 0 < n
  dim : ℕ
  dim_pos : 0 < dim
  encode : (Fin n → Fin a) → Matrix (Fin dim) (Fin dim) ℂ
  encoded_state : ∀ w, IsDensityMatrix (encode w)
  decode : Superop (Fin dim) (Fin n → Fin d)
  decoder_channel : IsChannel decode

/-- PDF p.7: average overlap fidelity of the actual code. -/
def SourceCode.fidelity {a d n : ℕ} {S : PureSource a d} (c : SourceCode S n) : ℝ :=
  ∑ w, S.weight w * effectProb (c.decode (c.encode w)) (S.word w)

/-- PDF p.8: average half-trace-norm distortion. -/
def SourceCode.distortion {a d n : ℕ} {S : PureSource a d} (c : SourceCode S n) : ℝ :=
  ∑ w, S.weight w * traceDistance (c.decode (c.encode w)) (S.word w)

/-- PDF p.11: log_2(dim K)/n, guarded by the code's positive dimension and length. -/
def SourceCode.rate {a d n : ℕ} {S : PureSource a d} (c : SourceCode S n) : ℝ :=
  Real.logb 2 c.dim / n

/-- PDF pp.7-8: a quantum encoding extends the given state-valued encoder by one
fixed CPTP map on every matrix, including off-diagonal operators. -/
def EncoderExtension {a d n : ℕ} {S : PureSource a d} (c : SourceCode S n)
    (E : Superop (Fin n → Fin d) (Fin c.dim)) : Prop :=
  IsChannel E ∧ ∀ w, E (S.word w) = c.encode w

/-- PDF p.8: a specific purification with reference first, obtained by vectorizing
sqrt(rho); its partial trace over the reference is rho for every density operator. -/
def purification {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    Matrix (I × I) (I × I) ℂ :=
  fun a b => cfc Real.sqrt rho a.2 a.1 * conj (cfc Real.sqrt rho b.2 b.1)

/-- PDF p.8: source-state entanglement fidelity, using the actual extended channel. -/
def sourceFe {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (T : Superop I I) : ℝ :=
  effectProb (idTensorSuperop (R := I) T (purification rho)) (purification rho)

/-- PDF pp.11,19: the four operational code qualities used in Chapter I. -/
inductive SourceQuality where
  | arbitraryFidelity | quantumFidelity | quantumEntanglement | arbitraryDistortion

/-- PDF pp.11,19: quality of an actual block code. No quantum extension is assumed
for arbitrary encoding, and entanglement fidelity is only evaluated on a CPTP extension. -/
def MeetsQuality {a d n : ℕ} {S : PureSource a d} (c : SourceCode S n)
    (q : SourceQuality) (lambda : ℝ) : Prop :=
  match q with
  | .arbitraryFidelity => 1 - c.fidelity ≤ lambda
  | .arbitraryDistortion => c.distortion ≤ lambda
  | .quantumFidelity => (∃ E, EncoderExtension c E) ∧ 1 - c.fidelity ≤ lambda
  | .quantumEntanglement => ∃ E, EncoderExtension c E ∧
      1 - sourceFe (copies n S.average) (c.decode ∘ E) ≤ lambda

/-- PDF p.11: minimum rate among actual codes; the extended nonnegative real
infimum is +infinity on an empty feasible set, never a spurious zero. -/
def minimumSourceRate {a d : ℕ} (S : PureSource a d) (q : SourceQuality)
    (n : ℕ) (lambda : ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ c : SourceCode S n, MeetsQuality c q lambda ∧ r = ENNReal.ofReal c.rate}

/-- PDF p.11: fixed-error operational limsup of block minima; n+1 ranges exactly
over all positive lengths. -/
def sourceRate {a d : ℕ} (S : PureSource a d) (q : SourceQuality) (lambda : ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun n : ℕ => minimumSourceRate S q (n+1) lambda) Filter.atTop

/-- PDF p.16: the actual compression map into the range coordinates of an isometry V.
For a state the second coefficient is (1-Tr(rho Pi))/k. -/
def projectionEncoder {I : Type*} [Fintype I] {k : ℕ}
    (V : Matrix I (Fin k) ℂ) : Superop I (Fin k) :=
  fun rho => Vᴴ * rho * V + ((rho.trace - (rho * (V * Vᴴ)).trace) / (k : ℂ)) • 1

example {a d : ℕ} (S : PureSource a d) (w : Fin 0 → Fin a) : S.weight w = 1 := by
  simp [PureSource.weight]

example {a d : ℕ} {S : PureSource a d} (lambda : ℝ) :
    minimumSourceRate S .arbitraryFidelity 0 lambda = ⊤ := by
  have hc : IsEmpty (SourceCode S 0) := ⟨fun c => (Nat.lt_irrefl 0 c.length_pos)⟩
  letI := hc
  simp [minimumSourceRate]

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

/-- PDF pp.60-61: a finite C*-algebra in a multiplicity-free direct-sum representation.
Its ordinary matrix trace is intrinsic; dim is the SUM of block Hilbert dimensions. -/
structure IntrinsicSystem where
  dim : ℕ
  positive : 0 < dim
  block : Fin dim → ℕ

/-- PDF p.61: intrinsic normalized states, including classical and hybrid systems. -/
def IntrinsicSystem.IsState (A : IntrinsicSystem) (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) : Prop :=
  IsDensityMatrix rho ∧ InBlocks A.block rho

/-- PDF p.61: minimal intrinsic projections, represented by rank-one block states. -/
def IntrinsicSystem.IsPureState (A : IntrinsicSystem) (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) : Prop :=
  QAlgorithms.Papers.Independent.Information100.P08.IsPure rho ∧ InBlocks A.block rho

/-- PDF p.62: matrix amplification of a Heisenberg map, preserving the ancillary
matrix blocks, not just diagonal ancillary states. -/
def intrinsicAmplification {A B : IntrinsicSystem}
    (F : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin B.dim) (Fin B.dim) ℂ)
    (m : ℕ) (T : Matrix (Fin m × Fin A.dim) (Fin m × Fin A.dim) ℂ) :
    Matrix (Fin m × Fin B.dim) (Fin m × Fin B.dim) ℂ :=
  fun a b => F (fun i j => T (a.1,i) (b.1,j)) a.2 b.2

/-- PDF p.62: a CP-unital Heisenberg map on the specified block algebras. Its
linear extension off the domain algebra is immaterial and is not assumed positive. -/
structure IntrinsicOperation (A B : IntrinsicSystem) where
  map : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin B.dim) (Fin B.dim) ℂ
  blocks : ∀ T, InBlocks A.block T → InBlocks B.block (map T)
  unit : map 1 = 1
  cp : ∀ (m : ℕ) (T : Matrix (Fin m × Fin A.dim) (Fin m × Fin A.dim) ℂ),
    (∀ a b, A.block a.2 ≠ A.block b.2 → T a b = 0) →
    T.PosSemidef → (intrinsicAmplification map m T).PosSemidef

/-- PDF pp.61,65: a subsystem inclusion, in independent intrinsic coordinates.
No tensor-factor representation or disjointness is imposed. -/
structure Embedding (A B : IntrinsicSystem) extends IntrinsicOperation A B where
  mul : ∀ T U, InBlocks A.block T → InBlocks A.block U → map (T * U) = map T * map U
  star : ∀ T, InBlocks A.block T → map Tᴴ = (map T)ᴴ
  faithful : ∀ T U, InBlocks A.block T → InBlocks A.block U → map T = map U → T = U

/-- PDF p.66: a star homomorphism, which is not required injective. -/
structure Hom (A B : IntrinsicSystem) extends IntrinsicOperation A B where
  mul : ∀ T U, InBlocks A.block T → InBlocks A.block U → map (T * U) = map T * map U
  star : ∀ T, InBlocks A.block T → map Tᴴ = (map T)ᴴ

/-- PDF pp.62,65: elementwise compatibility of two map images. -/
def CommutingImages {A B C : IntrinsicSystem}
    (F : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (G : Matrix (Fin B.dim) (Fin B.dim) ℂ →ₗ[ℂ] Matrix (Fin C.dim) (Fin C.dim) ℂ) : Prop :=
  ∀ T U, InBlocks A.block T → InBlocks B.block U → F T * G U = G U * F T

/-- PDF pp.62,65-69: the intrinsic trace adjoint, using only matrix units that
belong to the domain algebra. This is restriction for an inclusion map. -/
def intrinsicRestriction (A : IntrinsicSystem) {B : IntrinsicSystem}
    (F : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin B.dim) (Fin B.dim) ℂ)
    (rho : Matrix (Fin B.dim) (Fin B.dim) ℂ) : Matrix (Fin A.dim) (Fin A.dim) ℂ :=
  fun i j => if A.block i = A.block j then (rho * F (Matrix.single j i 1)).trace else 0

/-- PDF p.69: H(phi)=H(phi_*rho), for the one fixed ambient state rho. -/
def viewedEntropy (A : IntrinsicSystem) {B : IntrinsicSystem}
    (F : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin B.dim) (Fin B.dim) ℂ)
    (rho : Matrix (Fin B.dim) (Fin B.dim) ℂ) : ℝ := vnEntropy (intrinsicRestriction A F rho)

/-- PDF pp.66,69: the state pulled back by the product map F G. Compatibility
makes this a joint state; central overlaps are allowed. -/
def jointState (A B : IntrinsicSystem) {C : IntrinsicSystem}
    (F : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (G : Matrix (Fin B.dim) (Fin B.dim) ℂ →ₗ[ℂ] Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (rho : Matrix (Fin C.dim) (Fin C.dim) ℂ) :
    Matrix (Fin A.dim × Fin B.dim) (Fin A.dim × Fin B.dim) ℂ :=
  fun i j => if A.block i.1 = A.block j.1 ∧ B.block i.2 = B.block j.2 then
    (rho * (F (Matrix.single j.1 i.1 1) * G (Matrix.single j.2 i.2 1))).trace else 0

/-- PDF pp.65,69: mutual information, formed from the same ambient rho throughout. -/
def intrinsicMutualInformation (A B : IntrinsicSystem) {C : IntrinsicSystem}
    (F : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (G : Matrix (Fin B.dim) (Fin B.dim) ℂ →ₗ[ℂ] Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (rho : Matrix (Fin C.dim) (Fin C.dim) ℂ) : ℝ :=
  viewedEntropy A F rho + viewedEntropy B G rho - vnEntropy (jointState A B F G rho)

/-- PDF pp.65,69: conditional entropy; it may be negative. -/
def intrinsicConditionalEntropy (A B : IntrinsicSystem) {C : IntrinsicSystem}
    (F : Matrix (Fin A.dim) (Fin A.dim) ℂ →ₗ[ℂ] Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (G : Matrix (Fin B.dim) (Fin B.dim) ℂ →ₗ[ℂ] Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (rho : Matrix (Fin C.dim) (Fin C.dim) ℂ) : ℝ :=
  vnEntropy (jointState A B F G rho) - viewedEntropy B G rho

/-- PDF pp.62,68: joint pullback for any finite family. Product order is fixed by
the finite list; theorems require distinct images to commute, so the choice is irrelevant. -/
def familyState {I : Type*} [Fintype I] [DecidableEq I] (A : I → IntrinsicSystem) {C : IntrinsicSystem}
    (F : ∀ i, Matrix (Fin (A i).dim) (Fin (A i).dim) ℂ →ₗ[ℂ]
      Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (rho : Matrix (Fin C.dim) (Fin C.dim) ℂ) :
    Matrix (∀ i, Fin (A i).dim) (∀ i, Fin (A i).dim) ℂ :=
  fun a b => if ∀ i, (A i).block (a i) = (A i).block (b i) then
    (rho * ((Finset.univ : Finset I).toList.map fun i => F i (Matrix.single (b i) (a i) 1)).prod).trace
    else 0

/-- PDF pp.65,68: entropy of the generated algebra of a subset of a compatible family,
computed by the trace adjoint of multiplication, which preserves its intrinsic spectrum. -/
def familyEntropy {I : Type*} [Fintype I] [DecidableEq I] (A : I → IntrinsicSystem) {C : IntrinsicSystem}
    (F : ∀ i, Matrix (Fin (A i).dim) (Fin (A i).dim) ℂ →ₗ[ℂ]
      Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (rho : Matrix (Fin C.dim) (Fin C.dim) ℂ) (J : Finset I) : ℝ :=
  vnEntropy (familyState (fun i : {i // i ∈ J} => A i.val) (fun i => F i.val) rho)

/-- PDF pp.66-67: positive-coefficient diagonalization of a state, on its support;
zero eigenspaces are not required in this definition. -/
def Diagonalization (A : IntrinsicSystem) {m : ℕ} (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (p : Fin m → ℝ) (P : Fin m → Matrix (Fin A.dim) (Fin A.dim) ℂ) : Prop :=
  (∀ i, 0 < p i) ∧ (∀ i, A.IsPureState (P i)) ∧
  (∀ i j, i ≠ j → P i * P j = 0) ∧ rho = ∑ i, (p i : ℂ) • P i

/-- PDF p.70: the source's maximality condition, on positive domain elements. -/
def TraceNonincreasing {A B : IntrinsicSystem} (F : IntrinsicOperation A B) : Prop :=
  ∀ T, InBlocks A.block T → T.PosSemidef → (F.map T).trace.re ≤ T.trace.re

/-- PDF pp.64-65: nonnegative base-two relative-entropy contribution. The
continuous zero-first-mass value is q / log 2, so the linear corrections sum
to zero for normalized laws, including laws with zero entries. This form
avoids undefined infinity-minus-infinity for countably many outcomes. -/
def classicalKLTerm (p q : ℝ) : ℝ≥0∞ :=
  if p = 0 then ENNReal.ofReal (q / Real.log 2) else if q = 0 then ⊤ else
    ENNReal.ofReal (p * Real.logb 2 (p / q) + (q - p) / Real.log 2)

/-- PDF pp.62,65: entropy of a countable probability law, possibly +infinity. -/
def countableEntropy {B : Type*} (p : B → ℝ) : ℝ≥0∞ :=
  ∑' b, ENNReal.ofReal (-p b * Real.logb 2 (p b))

/-- PDF p.72: the actual outcome-law mutual information of commuting observables. -/
def measuredInformation {B D : Type*} {A : IntrinsicSystem}
    (X : B → Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (Y : D → Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) : ℝ≥0∞ :=
  ∑' z : B × D, classicalKLTerm (effectProb rho (X z.1 * Y z.2))
    (effectProb rho (X z.1) * effectProb rho (Y z.2))

/-- PDF pp.70,72: mutual information between an intrinsic subsystem and a countable
observable, as the weighted divergence of its posterior states from its marginal. -/
def hybridInformation (X : IntrinsicSystem) {A : IntrinsicSystem} {B : Type*}
    (E : Embedding X A) (D : B → Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) : ℝ≥0∞ :=
  ∑' b, ENNReal.ofReal (effectProb rho (D b)) *
    relativeBits
      (((effectProb rho (D b))⁻¹ : ℂ) •
        intrinsicRestriction X E.map (cfc Real.sqrt (D b) * rho * cfc Real.sqrt (D b)))
      (intrinsicRestriction X E.map rho)

/-- PDF p.73: the usual entrywise Borel structure on finite complex matrices.
It is the Borel structure for the finite-dimensional operator-norm topology. -/
local instance matrixMeasurableSpace {I J : Type*} [Fintype I] [Fintype J] :
    MeasurableSpace (Matrix I J ℂ) :=
  inferInstanceAs (MeasurableSpace (I → J → ℂ))

/-- PDF p.73: average state for an arbitrary measurable input law. -/
def cqAverage {X : Type*} [MeasurableSpace X] {I : Type*} [Fintype I]
    (mu : Measure X) (W : X → Matrix I I ℂ) := ∫ x, W x ∂mu

/-- PDF p.73: cq mutual information, defined by relative entropy before invoking
the entropy-difference identity, including arbitrary input probability measures. -/
def cqInformation {X : Type*} [MeasurableSpace X] {I : Type*} [Fintype I] [DecidableEq I]
    (mu : Measure X) (W : X → Matrix I I ℂ) : ℝ≥0∞ :=
  ∫⁻ x, relativeBits (W x) (cqAverage mu W) ∂mu

/-- PDF pp.37,73: measured information from the conditional and marginal outcome
laws of the actual POVM, including countably many outcomes. -/
def cqMeasuredInformation {X B : Type*} [MeasurableSpace X] {I : Type*}
    [Fintype I] [DecidableEq I] (mu : Measure X) (W : X → Matrix I I ℂ)
    (D : B → Matrix I I ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ∑' b, classicalKLTerm (effectProb (W x) (D b))
    (effectProb (cqAverage mu W) (D b)) ∂mu

example : classicalKLTerm 0 0 = 0 := by simp [classicalKLTerm]

example {A B : IntrinsicSystem} (F : IntrinsicOperation A B) :
    F.map 1 = 1 := F.unit

/-- PDF pp.60-61: a full matrix system in intrinsic coordinates. -/
def fullAlgebra (d : ℕ) (hd : 0 < d) : IntrinsicSystem := ⟨d, hd, fun _ => 0⟩

/-- PDF pp.61,65: the identity is a CP-unital operation on every intrinsic system. -/
def identityOperation (A : IntrinsicSystem) : IntrinsicOperation A A where
  map := LinearMap.id
  blocks := fun _ h => h
  unit := rfl
  cp := fun _ _ _ h => h

/-- PDF p.65: identity subsystem, used for sanity checks of restriction. -/
def identityEmbedding (A : IntrinsicSystem) : Embedding A A where
  toIntrinsicOperation := identityOperation A
  mul := fun _ _ _ _ => rfl
  star := fun _ _ => rfl
  faithful := fun _ _ _ _ h => h

example (A : IntrinsicSystem) (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (h : InBlocks A.block rho) : intrinsicRestriction A (identityEmbedding A).map rho = rho := by
  ext i j
  by_cases hij : A.block i = A.block j
  · simp [intrinsicRestriction, identityEmbedding, identityOperation, hij, Matrix.trace_mul_single]
  · simp [intrinsicRestriction, hij, h i j hij]

/-- PDF p.74: two copies of the finite factor index, labelled as X and Y. -/
def xIndices (n : ℕ) : Finset (Fin n × Bool) := Finset.univ.filter fun i => i.2 = false

/-- PDF p.74: the Y labels, separate from the X labels. -/
def yIndices (n : ℕ) : Finset (Fin n × Bool) := Finset.univ.filter fun i => i.2 = true

/-- PDF pp.69-70: joint state of a finite observable and a compatible intrinsic
subsystem, with the observable's actual outcome retained. -/
def observableJoint {B : Type*} [Fintype B] [DecidableEq B] {Y A : IntrinsicSystem}
    (E : Embedding Y A) (X : B → Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) :
    Matrix (B × Fin Y.dim) (B × Fin Y.dim) ℂ :=
  fun a b => if a.1 = b.1 then
    intrinsicRestriction Y E.map (cfc Real.sqrt (X a.1) * rho * cfc Real.sqrt (X a.1)) a.2 b.2 else 0

/-- PDF pp.53-55: a possibly correlated finite classical/hybrid pure-letter source.
The law is joint on all classical letters and the pure Y letter; it need not factor. -/
structure HybridSource (s : ℕ) where
  alphabet : Fin s → ℕ
  alphabet_pos : ∀ i, 0 < alphabet i
  system : IntrinsicSystem
  pure_count : ℕ
  pure_count_pos : 0 < pure_count
  letter : Fin pure_count → Matrix (Fin system.dim) (Fin system.dim) ℂ
  pure : ∀ p, system.IsPureState (letter p)
  distinct : Function.Injective letter
  law : PMF ((∀ i, Fin (alphabet i)) × Fin pure_count)

/-- PDF pp.53,57: the computed marginal state on X(J)Y of the joint source law. -/
def HybridSource.marginal {s : ℕ} (S : HybridSource s) (J : Finset (Fin s)) :
    Matrix (QAlgorithms.Papers.Independent.Claimed50.P40.Letters S.alphabet J × Fin S.system.dim)
      (QAlgorithms.Papers.Independent.Claimed50.P40.Letters S.alphabet J × Fin S.system.dim) ℂ :=
  fun a b => if a.1 = b.1 then
    ∑ x, if QAlgorithms.Papers.Independent.Claimed50.P40.Matches J x.1 a.1 then
      ((S.law x).toReal : ℂ) * S.letter x.2 a.2 b.2 else 0
    else 0

/-- PDF pp.57-58: H(X(J)|YX(J^c)), computed from the same correlated source. -/
def HybridSource.subsetEntropy {s : ℕ} (S : HybridSource s) (J : Finset (Fin s)) : ℝ :=
  vnEntropy (S.marginal Finset.univ) - vnEntropy (S.marginal Jᶜ)

/-- PDF pp.57-58: upward unbounded source rate region, with lower subset constraints. -/
def HybridSource.lowerRegion {s : ℕ} (S : HybridSource s) : Set (Fin s → ℝ) :=
  {R | ∀ J : Finset (Fin s), S.subsetEntropy J ≤ ∑ i ∈ J, R i}

/-- PDF p.58: source permutation corner, conditioned on the preceding classical
letters and Y, with the source's order rather than its reverse. -/
def HybridSource.corner {s : ℕ} (S : HybridSource s) (pi : Equiv.Perm (Fin s)) : Fin s → ℝ :=
  fun a =>
    let J := QAlgorithms.Papers.Independent.Claimed50.P40.predecessors pi (pi.symm a)
    vnEntropy (S.marginal (insert a J)) - vnEntropy (S.marginal J)

/-- PDF p.57: ordinary extremality; no coordinatewise upper-maximality condition. -/
def IsExtreme {I : Type*} (S : Set (I → ℝ)) (R : I → ℝ) : Prop :=
  R ∈ S ∧ ∀ a ∈ S, ∀ b ∈ S, ∀ t : ℝ, 0 < t → t < 1 →
    R = t • a + (1 - t) • b → a = R ∧ b = R

example {s : ℕ} (S : HybridSource s) : S.subsetEntropy ∅ = 0 := by
  unfold HybridSource.subsetEntropy
  rw [Finset.compl_empty]
  exact sub_self _

/-- PDF p.29: empirical law weights; the source calls this the type of the word.
Positive n is required in every theorem using this definition. -/
def empiricalWeight {a n : ℕ} (w : Fin n → Fin a) (x : Fin a) : ℝ := count w x / (n : ℝ)

/-- PDF p.29: conditional output entropy for the actual word's empirical law. -/
def wordConditionalEntropy {a d n : ℕ} (S : Fin a → FineResolution d) (w : Fin n → Fin a) : ℝ :=
  ∑ x, empiricalWeight w x * vnEntropy (S x).state

/-- PDF p.29: conditional variance-typical projector. Equal input letters are
grouped in the count conditions; the tensor factors remain in their original time order.
An empty input-letter group imposes only 0≤0 and contributes the scalar identity. -/
def conditionalVarianceProjector {a d n : ℕ} (S : Fin a → FineResolution d)
    (w : Fin n → Fin a) (delta : ℝ) :=
  ∑ j ∈ (Finset.univ.filter fun j : Fin n → Fin d => ∀ x r,
    |((Finset.univ.filter fun k => w k = x ∧ j k = r).card : ℝ) -
      count w x * ((S x).law r).toReal| ≤
      delta * Real.sqrt (count w x) *
        Real.sqrt (((S x).law r).toReal * (1 - ((S x).law r).toReal))),
    wordTensor (fun k => (S (w k)).atom (j k))

/-- PDF pp.30-31: change the eigenvalue list in a chosen simultaneous fine basis. -/
def changeSpectrum {d : ℕ} (S : FineResolution d) (P : PMF (Fin d)) : FineResolution d :=
  { S with
    weight := fun j => (P j).toReal
    nonneg := fun j => ENNReal.toReal_nonneg
    total := by
      have ht : ∑ j : Fin d, P j = 1 := by
        simpa only [tsum_fintype] using P.tsum_coe
      calc
        ∑ j, (P j).toReal = (∑ j, P j).toReal :=
          (ENNReal.toReal_sum (fun j _ => P.apply_ne_top j)).symm
        _ = 1 := by rw [ht]; simp }

/-- PDF p.31: base-two divergence tail, with 2^{-n*infinity}=0 at positive n. -/
def divergenceTail (n : ℕ) (D : ℝ≥0∞) : ℝ :=
  if D = ⊤ then 0 else exp2 (-(n : ℝ) * D.toReal)

example (n : ℕ) : divergenceTail n ⊤ = 0 := by simp [divergenceTail]

/-- PDF pp.45-46: the regrouped multi-party basis, with each sender holding a word. -/
abbrev PartyWords {s : ℕ} (A : Fin s → IntrinsicSystem) (n : ℕ) := ∀ i, Fin n → Fin (A i).dim

/-- PDF p.45: finite pure-letter source data. Validity is stated separately so that
explicit example ensembles can be constructed without admitted definition proofs. -/
structure MultipleData (s : ℕ) (L : Type*) [Fintype L] where
  system : Fin s → IntrinsicSystem
  law : PMF L
  letter : L → Matrix (∀ i, Fin (system i).dim) (∀ i, Fin (system i).dim) ℂ

/-- PDF p.45: source validity, with no product-state promise or independent sender law. -/
def MultipleData.Valid {s : ℕ} {L : Type*} [Fintype L] (S : MultipleData s L) : Prop :=
  (∀ x, IsPure (S.letter x)) ∧ Function.Injective S.letter ∧
  ∀ x u v, (∃ i, (S.system i).block (u i) ≠ (S.system i).block (v i)) → S.letter x u v = 0

/-- PDF p.45: computed average source density. -/
def MultipleData.average {s : ℕ} {L : Type*} [Fintype L] (S : MultipleData s L) :=
  ∑ x, ((S.law x).toReal : ℂ) • S.letter x

/-- PDF pp.45-46: the actual temporal word, regrouped by sender. -/
def MultipleData.word {s n : ℕ} {L : Type*} [Fintype L] (S : MultipleData s L)
    (w : Fin n → L) : Matrix (PartyWords S.system n) (PartyWords S.system n) ℂ :=
  fun a b => ∏ t, S.letter (w t) (fun i => a i t) (fun i => b i t)

/-- PDF p.46: the average block state, in the same party grouping as the encoder. -/
def MultipleData.blockAverage {s : ℕ} {L : Type*} [Fintype L] (S : MultipleData s L) (n : ℕ) :
    Matrix (PartyWords S.system n) (PartyWords S.system n) ℂ :=
  fun a b => ∏ t, S.average (fun i => a i t) (fun i => b i t)

/-- PDF p.45: partial trace to any sender subset, including the empty subset. -/
def multipleMarginal {s : ℕ} (A : Fin s → IntrinsicSystem)
    (rho : Matrix (∀ i, Fin (A i).dim) (∀ i, Fin (A i).dim) ℂ) (J : Finset (Fin s)) :
    Matrix (∀ i : {i // i ∈ J}, Fin (A i.val).dim)
      (∀ i : {i // i ∈ J}, Fin (A i.val).dim) ℂ :=
  fun a b => ∑ u, ∑ v,
    if (∀ i : {i // i ∈ J}, u i.val = a i ∧ v i.val = b i) ∧
      (∀ i, i ∉ J → u i = v i) then rho u v else 0

/-- PDF p.45: tensor product of heterogeneous local maps, on all matrix units.
This preserves entangled source letters and does not replace them by their marginals. -/
def partyMaps {s : ℕ} (A : Fin s → IntrinsicSystem) (n : ℕ) (k : Fin s → ℕ)
    (E : ∀ i, Superop (Fin n → Fin (A i).dim) (Fin (k i))) :
    Superop (PartyWords A n) (∀ i, Fin (k i)) :=
  fun T a b => ∑ u, ∑ v, T u v * ∏ i, E i (Matrix.single (u i) (v i) 1) (a i) (b i)

/-- PDF pp.45-46: joint CPTP decoder with range in the actual product block algebra.
CPTP extensions from intrinsic input algebras to full matrices are equivalent by
precomposing block pinching. This imposes no restriction on intrinsic local encoders. -/
structure MultipleCode {s : ℕ} {L : Type*} [Fintype L] (S : MultipleData s L) (n : ℕ) where
  length_pos : 0 < n
  dim : Fin s → ℕ
  dim_pos : ∀ i, 0 < dim i
  encode : ∀ i, Superop (Fin n → Fin (S.system i).dim) (Fin (dim i))
  encoder_channel : ∀ i, IsChannel (encode i)
  decode : Superop (∀ i, Fin (dim i)) (PartyWords S.system n)
  decoder_channel : IsChannel decode
  output_blocks : ∀ T, T.PosSemidef → ∀ u v,
    (∃ i t, (S.system i).block (u i t) ≠ (S.system i).block (v i t)) → decode T u v = 0

/-- PDF p.46: the full joint source recovery channel. -/
def MultipleCode.channel {s n : ℕ} {L : Type*} [Fintype L] {S : MultipleData s L}
    (c : MultipleCode S n) : Superop (PartyWords S.system n) (PartyWords S.system n) :=
  c.decode ∘ partyMaps S.system n c.dim c.encode

/-- PDF p.46: rate of each actual local compression space. -/
def MultipleCode.rate {s n : ℕ} {L : Type*} [Fintype L] {S : MultipleData s L}
    (c : MultipleCode S n) (i : Fin s) : ℝ := Real.logb 2 (c.dim i) / n

/-- PDF p.46: ensemble-averaged pure-word fidelity. -/
def MultipleCode.fidelity {s n : ℕ} {L : Type*} [Fintype L] {S : MultipleData s L}
    (c : MultipleCode S n) : ℝ :=
  ∑ w : Fin n → L, (∏ t, (S.law (w t)).toReal) * effectProb (c.channel (S.word w)) (S.word w)

/-- PDF p.46: ensemble-averaged half trace distance. -/
def MultipleCode.distortion {s n : ℕ} {L : Type*} [Fintype L] {S : MultipleData s L}
    (c : MultipleCode S n) : ℝ :=
  ∑ w : Fin n → L, (∏ t, (S.law (w t)).toReal) * traceDistance (c.channel (S.word w)) (S.word w)

/-- PDF p.46: actual code-sequence rate region; error vanishes and every rate
coordinate converges to the specified rate, over all positive lengths. -/
def quantumSourceRegion {s : ℕ} {L : Type*} [Fintype L] (S : MultipleData s L)
    (distortion : Bool := false) : Set (Fin s → ℝ) :=
  {R | ∃ c : ∀ n, MultipleCode S (n+1),
    (∀ i, Tendsto (fun n => (c n).rate i) atTop (nhds (R i))) ∧
    Tendsto (fun n => if distortion then (c n).distortion else 1 - (c n).fidelity) atTop (nhds 0)}

/-- PDF p.46: Fe only for fully quantum systems. The explicit domain guard
prevents an assertion of a purification rate region on a hybrid system. -/
def entanglementSourceRegion {s : ℕ} {L : Type*} [Fintype L] (S : MultipleData s L)
    (_fullyQuantum : ∀ i a b, (S.system i).block a = (S.system i).block b) : Set (Fin s → ℝ) :=
  {R | ∃ c : ∀ n, MultipleCode S (n+1),
    (∀ i, Tendsto (fun n => (c n).rate i) atTop (nhds (R i))) ∧
    Tendsto (fun n => 1 - sourceFe (S.blockAverage (n+1)) (c n).channel) atTop (nhds 0)}

/-- PDF pp.53-55: intrinsic systems, with Y the last party. -/
def HybridSource.systems {s : ℕ} (S : HybridSource s) : Fin (s+1) → IntrinsicSystem :=
  Fin.lastCases S.system (fun i => ⟨S.alphabet i, S.alphabet_pos i, Fin.val⟩)

/-- Read a classical coordinate through the fixed dependent-system identification. -/
def HybridSource.classicalCoordinate {s : ℕ} (S : HybridSource s)
    (a : ∀ i, Fin (S.systems i).dim) (i : Fin s) : Fin (S.alphabet i) :=
  Fin.cast (by simp [HybridSource.systems]) (a i.castSucc)

/-- Read Y through the same fixed dependent-system identification. -/
def HybridSource.quantumCoordinate {s : ℕ} (S : HybridSource s)
    (a : ∀ i, Fin (S.systems i).dim) : Fin S.system.dim :=
  Fin.cast (by simp [HybridSource.systems]) (a (Fin.last s))

/-- PDF pp.53-55: the actual joint classical/pure-Y source, with Y the last party. -/
def HybridSource.multiple {s : ℕ} (S : HybridSource s) :
    MultipleData (s+1) ((∀ i, Fin (S.alphabet i)) × Fin S.pure_count) where
  system := S.systems
  law := S.law
  letter := fun x a b =>
    if (∀ i : Fin s, S.classicalCoordinate a i = x.1 i ∧ S.classicalCoordinate b i = x.1 i) then
      S.letter x.2 (S.quantumCoordinate a) (S.quantumCoordinate b) else 0

/-- PDF pp.55-56: append the entropy of Y to the classical compression rates. -/
def HybridSource.withYRate {s : ℕ} (S : HybridSource s) (R : Fin s → ℝ) : Fin (s+1) → ℝ :=
  Fin.lastCases (vnEntropy (S.marginal ∅)) R

/-- PDF pp.45-46: product-letter data for arbitrary local encoders. The JOINT law
may be correlated; only each source letter is a product across senders. -/
structure ProductData (s : ℕ) where
  system : Fin s → IntrinsicSystem
  alphabet : Fin s → ℕ
  law : PMF (∀ i, Fin (alphabet i))
  localLetter : ∀ i, Fin (alphabet i) → Matrix (Fin (system i).dim) (Fin (system i).dim) ℂ

/-- PDF pp.45-46: normalized distinct local pure letters in the respective intrinsic systems. -/
def ProductData.Valid {s : ℕ} (S : ProductData s) : Prop :=
  (∀ i, 0 < S.alphabet i) ∧ (∀ i x, (S.system i).IsPureState (S.localLetter i x)) ∧
  ∀ i, Function.Injective (S.localLetter i)

/-- PDF p.45: construct the joint pure ensemble from local product letters and the
original correlated law, rather than replacing that law by a product of marginals. -/
def ProductData.multiple {s : ℕ} (S : ProductData s) : MultipleData s (∀ i, Fin (S.alphabet i)) :=
  ⟨S.system, S.law, fun x => wordTensor (fun i => S.localLetter i (x i))⟩

/-- PDF p.46: arbitrary separate state-valued encoders and an actual joint CPTP
decoder. Only the local word is supplied to each encoder. -/
structure ArbitraryMultipleCode {s : ℕ} (S : ProductData s) (n : ℕ) where
  length_pos : 0 < n
  dim : Fin s → ℕ
  dim_pos : ∀ i, 0 < dim i
  encode : ∀ i, (Fin n → Fin (S.alphabet i)) → Matrix (Fin (dim i)) (Fin (dim i)) ℂ
  encoded_state : ∀ i w, IsDensityMatrix (encode i w)
  decode : Superop (∀ i, Fin (dim i)) (PartyWords S.system n)
  decoder_channel : IsChannel decode
  output_blocks : ∀ T, T.PosSemidef → ∀ u v,
    (∃ i t, (S.system i).block (u i t) ≠ (S.system i).block (v i t)) → decode T u v = 0

/-- PDF p.46: actual average overlap quality for the arbitrary local encoders. -/
def ArbitraryMultipleCode.fidelity {s n : ℕ} {S : ProductData s}
    (c : ArbitraryMultipleCode S n) : ℝ :=
  ∑ w : Fin n → (∀ i, Fin (S.alphabet i)),
    (∏ t, (S.law (w t)).toReal) *
      effectProb (c.decode (wordTensor (fun i => c.encode i (fun t => w t i)))) (S.multiple.word w)

/-- PDF p.46: average half trace norm for the same arbitrary code. -/
def ArbitraryMultipleCode.distortion {s n : ℕ} {S : ProductData s}
    (c : ArbitraryMultipleCode S n) : ℝ :=
  ∑ w : Fin n → (∀ i, Fin (S.alphabet i)),
    (∏ t, (S.law (w t)).toReal) *
      traceDistance (c.decode (wordTensor (fun i => c.encode i (fun t => w t i)))) (S.multiple.word w)

/-- PDF p.46: arbitrary-encoding operational region, only on product-letter sources. -/
def arbitrarySourceRegion {s : ℕ} (S : ProductData s) (distortion : Bool := false) : Set (Fin s → ℝ) :=
  {R | ∃ c : ∀ n, ArbitraryMultipleCode S (n+1),
    (∀ i, Tendsto (fun n => Real.logb 2 ((c n).dim i) / (n+1 : ℝ)) atTop (nhds (R i))) ∧
    Tendsto (fun n => if distortion then (c n).distortion else 1 - (c n).fidelity) atTop (nhds 0)}

/-- PDF p.46: closed, convex and coordinatewise upward closed, including unbounded regions. -/
def SourceRegionProperties {s : ℕ} (T : Set (Fin s → ℝ)) : Prop :=
  IsClosed T ∧ Convex ℝ T ∧ ∀ R ∈ T, ∀ Rnew, (∀ i, R i ≤ Rnew i) → Rnew ∈ T

/-- PDF pp.47-48: the four wheel vectors |0>,|1>,|+>,|->, with real signs. -/
def wheelVector (x : Fin 4) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 fun b =>
    if x.val < 2 then (if b.val = x.val then 1 else 0) else
    if x.val = 3 ∧ b.val = 1 then -((Real.sqrt 2 : ℂ)⁻¹) else (Real.sqrt 2 : ℂ)⁻¹

/-- PDF pp.47-48: the actual cloned-wheel source, with the same randomly chosen
pure state sent to both encoders. Its law is diagonal, not independent across parties. -/
def clonedWheel : ProductData 2 where
  system := fun _ => fullAlgebra 2 (by decide)
  alphabet := fun _ => 4
  law := PMF.map (fun x : Fin 4 => fun _ : Fin 2 => x) (PMF.uniformOfFintype (Fin 4))
  localLetter := fun _ x => pureDensity (wheelVector x)

/-- PDF p.52: the two orthogonal alternatives of the cloned cross. -/
def clonedCross : ProductData 2 where
  system := fun _ => fullAlgebra 2 (by decide)
  alphabet := fun _ => 2
  law := PMF.map (fun x : Fin 2 => fun _ : Fin 2 => x) (PMF.uniformOfFintype (Fin 2))
  localLetter := fun _ x => pureDensity (ket x)

/-- PDF pp.51-52: the two Bell alternatives |Phi+> and |Phi->, in party coordinates. -/
def eprSourceVector (x : Fin 2) : EuclideanSpace ℂ (Fin 2 → Fin 2) :=
  WithLp.toLp 2 fun a => if a 0 = a 1 then
    (if x.val = 1 ∧ (a 0).val = 1 then -1 else 1) * (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- PDF p.51: the actual equidistributed EPR source. -/
def eprSource : MultipleData 2 (Fin 2) where
  system := fun _ => fullAlgebra 2 (by decide)
  law := PMF.uniformOfFintype (Fin 2)
  letter := fun x => pureDensity (eprSourceVector x)

/-- PDF pp.47-48: the necessary quantum cloned-wheel rate region. -/
def wheelQuantumOuter : Set (Fin 2 → ℝ) :=
  {R | 1/2 ≤ R 0 ∧ 1/2 ≤ R 1 ∧ 3/2 ≤ R 0 + R 1}

/-- PDF p.48: the arbitrary-encoding sum-rate region for a two-source example. -/
def nonnegativeSumRegion (h : ℝ) : Set (Fin 2 → ℝ) :=
  {R | 0 ≤ R 0 ∧ 0 ≤ R 1 ∧ h ≤ R 0 + R 1}

/-- PDF pp.51-52: the half-qubit individual-rate necessary constraints. -/
def halfRateRegion : Set (Fin 2 → ℝ) := {R | 1/2 ≤ R 0 ∧ 1/2 ≤ R 1}

example : wheelVector 0 0 = 1 := by norm_num [wheelVector]

example : eprSourceVector 0 (fun _ => (0 : Fin 2)) = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [eprSourceVector]

/-- PDF p.20: nonstationary channels are arbitrary nonempty measurable state sets
on the one fixed output system. Input laws need not have finite support. -/
structure StateChannel (A : IntrinsicSystem) where
  carrier : Set (Matrix (Fin A.dim) (Fin A.dim) ℂ)
  nonempty : carrier.Nonempty
  measurable : MeasurableSet carrier
  states : ∀ rho ∈ carrier, A.IsState rho

/-- PDF p.24: single-use capacity, optimized over all probability measures on the
measurable state set. Information is bounded by log_2(dim A's Hilbert representation),
so the real supremum is bounded and nonempty. -/
def StateChannel.capacity {A : IntrinsicSystem} (W : StateChannel A) : ℝ :=
  sSup {r | ∃ P : ProbabilityMeasure W.carrier,
    r = (cqInformation (P : Measure W.carrier) (fun x => x.val)).toReal}

/-- PDF pp.23-24: actual nonstationary product-state code with a collective block
POVM and a failure outcome. The error criterion is maximum message error. -/
structure NonstationaryCode {A : IntrinsicSystem} (W : ℕ → StateChannel A) (n : ℕ) where
  length_pos : 0 < n
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → (i : Fin n) → Matrix (Fin A.dim) (Fin A.dim) ℂ
  allowed : ∀ m i, encode m i ∈ (W i.val).carrier
  decode : Option (Fin messages) → Matrix (Fin n → Fin A.dim) (Fin n → Fin A.dim) ℂ
  povm : IsPOVM decode
  blocks : ∀ m, QAlgorithms.Papers.Independent.Claimed50.P40.InBlockPower A.block n (decode m)

/-- PDF p.23: maximum error, with the message-set nonemptiness enforced in the code. -/
def NonstationaryCode.error {A : IntrinsicSystem} {W : ℕ → StateChannel A} {n : ℕ}
    (c : NonstationaryCode W n) : ℝ :=
  (Finset.univ : Finset (Fin c.messages)).sup'
    ⟨⟨0, c.messages_pos⟩, Finset.mem_univ _⟩
    (fun m => 1 - effectProb (wordTensor (c.encode m)) (c.decode (some m)))

/-- PDF p.23: optimal number of messages among actual codes. For 0≤lambda<1 the
set is nonempty and bounded by dim(output)^n/(1-lambda), so Nat.sSup is an actual
finite maximum; no statement below uses this definition in the unbounded lambda≥1 regime. -/
def nonstationaryN {A : IntrinsicSystem} (W : ℕ → StateChannel A) (n : ℕ) (lambda : ℝ) : ℕ :=
  sSup {m | ∃ c : NonstationaryCode W n, c.messages = m ∧ c.error ≤ lambda}

/-- PDF pp.24-25: all maximal-code conclusions, including membership in the
large event and the trace bound for actual chosen entropy-typical projectors. -/
def MaximalCodeConclusion {A : IntrinsicSystem} {W : ℕ → StateChannel A} {n : ℕ}
    (P : ∀ i : Fin n, ProbabilityMeasure (W i.val).carrier)
    (event : Set (∀ i : Fin n, (W i.val).carrier)) (K delta lambda : ℝ)
    (projective : Bool) : Prop :=
  ∃ c : NonstationaryCode W n, c.error ≤ lambda ∧
    (∀ m, (fun (i : Fin n) => (⟨c.encode m i, c.allowed m i⟩ : (W i.val).carrier)) ∈ event) ∧
    (∃ S : Fin c.messages → Fin n → FineResolution A.dim,
      (∀ m i, (S m i).state = c.encode m i) ∧
      ∀ m, (c.decode (some m)).trace.re ≤ (entropyProjector (S m) delta).trace.re) ∧
    Real.logb 2 c.messages ≥
      (∑ i : Fin n, (cqInformation (P i : Measure (W i.val).carrier) (fun x => x.val)).toReal) -
        K * Real.sqrt n ∧
    (projective = true → ∀ m, c.decode (some m) * c.decode (some m) = c.decode (some m))

/-- PDF p.28: finite stationary channel, with input labels retained even when
several labels are mapped to the same output state. -/
structure FiniteChannel (a : ℕ) (A : IntrinsicSystem) where
  alphabet_pos : 0 < a
  state : Fin a → Matrix (Fin A.dim) (Fin A.dim) ℂ
  valid : ∀ x, A.IsState (state x)

/-- PDF pp.28-29: finite-law Holevo information, using the same normalized channel. -/
def FiniteChannel.information {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A) (P : PMF (Fin a)) : ℝ :=
  vnEntropy (∑ x, ((P x).toReal : ℂ) • W.state x) - ∑ x, (P x).toReal * vnEntropy (W.state x)

/-- PDF p.28: capacity of the finite channel; PMF is compact and nonempty, and
information is bounded. This real supremum has no empty/unbounded-set junk. -/
def FiniteChannel.capacity {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A) : ℝ :=
  sSup (Set.range W.information)

/-- PDF pp.23,28: finite stationary code, collective decoding, optional failure. -/
structure FiniteCode {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A) (n : ℕ) where
  length_pos : 0 < n
  messages : ℕ
  messages_pos : 0 < messages
  word : Fin messages → Fin n → Fin a
  decode : Option (Fin messages) → Matrix (Fin n → Fin A.dim) (Fin n → Fin A.dim) ℂ
  povm : IsPOVM decode
  blocks : ∀ m, QAlgorithms.Papers.Independent.Claimed50.P40.InBlockPower A.block n (decode m)

/-- PDF pp.23,28: maximum-message error for the actual channel and decoder. -/
def FiniteCode.error {a n : ℕ} {A : IntrinsicSystem} {W : FiniteChannel a A} (c : FiniteCode W n) : ℝ :=
  (Finset.univ : Finset (Fin c.messages)).sup'
    ⟨⟨0, c.messages_pos⟩, Finset.mem_univ _⟩
    (fun m => 1 - effectProb (wordTensor (fun i => W.state (c.word m i))) (c.decode (some m)))

/-- PDF p.28: actual optimal message count, finite whenever lambda<1. -/
def finiteN {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A) (n : ℕ) (lambda : ℝ) : ℕ :=
  sSup {m | ∃ c : FiniteCode W n, c.messages = m ∧ c.error ≤ lambda}

/-- PDF pp.28,33: the code really has a fixed empirical composition P. -/
def FiniteCode.Composition {a n : ℕ} {A : IntrinsicSystem} {W : FiniteChannel a A}
    (c : FiniteCode W n) (P : PMF (Fin a)) : Prop :=
  ∀ m x, empiricalWeight (c.word m) x = (P x).toReal

/-- PDF p.53: actual finite codebook, with duplicate encodings removed as a set. -/
def FiniteCode.codebook {a n : ℕ} {A : IntrinsicSystem} {W : FiniteChannel a A}
    (c : FiniteCode W n) : Finset (Fin n → Fin a) := Finset.univ.image c.word

/-- PDF p.20: an intrinsic-output source code must decode into the declared block
algebra. Quantum input maps may be extended by precomposing intrinsic block pinching. -/
def IntrinsicSourceCode {a n : ℕ} (A : IntrinsicSystem) {S : PureSource a A.dim} (c : SourceCode S n) : Prop :=
  ∀ T, T.PosSemidef →
    QAlgorithms.Papers.Independent.Claimed50.P40.InBlockPower A.block n (c.decode T)

/-- PDF p.20: fixed-error rates in the intrinsic source algebra; resource cost
is log Hilbert dimension of the compressed system, not dimension of the algebra. -/
def intrinsicSourceRate {a : ℕ} (A : IntrinsicSystem) (S : PureSource a A.dim)
    (quantum : Bool) (lambda : ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun n : ℕ => sInf {r | ∃ c : SourceCode S (n+1),
    IntrinsicSourceCode A c ∧ MeetsQuality c
      (if quantum then .quantumFidelity else .arbitraryFidelity) lambda ∧
      r = ENNReal.ofReal c.rate}) atTop

/-- PDF pp.28,34: H(V|P), for any finite family of output states. -/
def letterOutputEntropy {a d : ℕ} (P : PMF (Fin a))
    (V : Fin a → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ x, (P x).toReal * vnEntropy (V x)

/-- PDF pp.28,34: conditional quantum divergence, allowing unsupported output
states and zero-probability input letters (0*infinity=0 in ENNReal). -/
def conditionalDivergence {a d : ℕ} (P : PMF (Fin a))
    (V W : Fin a → Matrix (Fin d) (Fin d) ℂ) : ℝ≥0∞ :=
  ∑ x, ENNReal.ofReal (P x).toReal * relativeBits (V x) (W x)

/-- PDF p.34: individual entropy-threshold exponent, with empty infimum +infinity. -/
def individualExponent {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A)
    (P : PMF (Fin a)) (L : ℝ) : ℝ≥0∞ :=
  sInf {D | ∃ V : FiniteChannel a A, L < letterOutputEntropy P V.state ∧
    D = conditionalDivergence P V.state W.state}

/-- PDF p.34: collective entropy-threshold exponent. -/
def collectiveExponent {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A)
    (P : PMF (Fin a)) (L : ℝ) : ℝ≥0∞ :=
  sInf {D | ∃ rho : Matrix (Fin A.dim) (Fin A.dim) ℂ, A.IsState rho ∧ vnEntropy rho ≤ L ∧
    D = relativeBits rho (∑ x, ((P x).toReal : ℂ) • W.state x)}

/-- PDF p.34: E_g(R,P); the factor 1/2 multiplies ONLY the collective exponent.
The supremum is paired with an explicit attainment conclusion below. -/
def greedyExponent {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A)
    (R : ℝ) (P : PMF (Fin a)) : ℝ≥0∞ :=
  sSup {D | ∃ L Lprime : ℝ, R ≤ Lprime - L ∧
    D = min (individualExponent W P L) ((1/2 : ℝ≥0∞) * collectiveExponent W P Lprime)}

/-- PDF p.35: optimize the greedy bound over all rate-admissible input laws. -/
def greedyBound {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A) (R : ℝ) : ℝ≥0∞ :=
  sSup {D | ∃ P : PMF (Fin a), R ≤ W.information P ∧ D = greedyExponent W R P}

/-- PDF p.35: sphere-packing exponent, minimizing over the full normalized channel
class, with no commutativity restriction on comparison-channel states. -/
def sphereExponent {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A)
    (R : ℝ) (P : PMF (Fin a)) : ℝ≥0∞ :=
  sInf {D | ∃ V : FiniteChannel a A, V.information P ≤ R ∧
    D = conditionalDivergence P V.state W.state}

/-- PDF p.36: global sphere-packing bound. Attainment is stated below. -/
def sphereBound {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A) (R : ℝ) : ℝ≥0∞ :=
  sSup (Set.range (sphereExponent W R))

/-- PDF p.28: minimum maximum error among actual n-block codes at rate at least R. -/
def minimumChannelError {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A) (n : ℕ) (R : ℝ) : ℝ≥0∞ :=
  sInf {e | ∃ c : FiniteCode W n, (c.messages : ℝ) ≥ exp2 (n * R) ∧ e = ENNReal.ofReal c.error}

/-- PDF p.34: a zero error has exponent +infinity, not totalized log(0)=0. -/
def errorExponent (n : ℕ) (e : ℝ≥0∞) : ℝ≥0∞ :=
  if e = 0 then ⊤ else if e = ⊤ then 0 else ENNReal.ofReal (-Real.logb 2 e.toReal / n)

/-- PDF p.34: joint liminf in length tending to infinity and POSITIVE rate slack
tending to zero. It is not the error exponent at the exactly fixed finite-block rate. -/
def reliability {a : ℕ} {A : IntrinsicSystem} (W : FiniteChannel a A) (R : ℝ) : ℝ≥0∞ :=
  Filter.liminf (fun z : ℕ × ℝ =>
    errorExponent (z.1+1) (minimumChannelError W (z.1+1) (R-z.2)))
    ((atTop : Filter ℕ) ×ˢ nhdsWithin 0 (Set.Ioi 0))

example (n : ℕ) : errorExponent n 0 = ⊤ := by simp [errorExponent]

/-- PDF p.17: least common support over ALL states and ALL fine bases of entropy
at most R, not just the eigenbasis of the particular source being compressed. -/
def universalRange (d n : ℕ) (R : ℝ) : Submodule ℂ (EuclideanSpace ℂ (Fin n → Fin d)) :=
  Submodule.span ℂ {v | ∃ S : FineResolution d, vnEntropy S.state ≤ R ∧
    ∃ u : EuclideanSpace ℂ (Fin n → Fin d), v = act (varianceProjector S n 0) u}

/-- PDF p.17: the orthogonal projector onto the actual universal least common support. -/
def universalProjector (d n : ℕ) (R : ℝ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  fun a b => inner ℂ (ket a) ((universalRange d n R).starProjection (ket b))

/-- PDF p.17: entropy-constrained divergence infimum. An empty constraint set
has value +infinity and therefore a zero exponential tail. -/
def highEntropyDivergence {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (R : ℝ) : ℝ≥0∞ :=
  sInf {D | ∃ nu : Matrix I I ℂ, IsDensityMatrix nu ∧ R ≤ vnEntropy nu ∧ D = relativeBits nu rho}

/-- PDF p.31: finitely many realizable count vectors, with no uncountable sum. -/
def countTypes (d n : ℕ) : Finset (Fin d → ℕ) :=
  Finset.univ.image (fun w : Fin n → Fin d => fun j => count w j)

/-- PDF pp.30-31: exact spectral-type projector for a prescribed count vector. -/
def exactProjector {d : ℕ} (S : FineResolution d) (n : ℕ) (r : Fin d → ℕ) :=
  ∑ w ∈ (Finset.univ.filter fun w : Fin n → Fin d => ∀ j, count w j = r j),
    wordTensor (fun i => S.atom (w i))

/-- PDF p.31: state of a realizable spectral type; positive length is required below. -/
def spectralTypeState {d : ℕ} (S : FineResolution d) (n : ℕ) (r : Fin d → ℕ) :=
  ∑ j, ((r j / (n : ℝ) : ℝ) : ℂ) • S.atom j

/-- PDF p.31: the entropy-high spectral projector is a finite sum of exact types. -/
def highEntropyProjector {d : ℕ} (S : FineResolution d) (n : ℕ) (L : ℝ) :=
  ∑ r ∈ ((countTypes d n).filter fun r => L ≤ vnEntropy (spectralTypeState S n r)),
    exactProjector S n r

/-- PDF p.31: realizable conditional count tables for a fixed input word. -/
def conditionalTypes {a n : ℕ} (d : ℕ) (w : Fin n → Fin a) : Finset (Fin a → Fin d → ℕ) :=
  Finset.univ.image (fun j : Fin n → Fin d => fun x r =>
    (Finset.univ.filter fun t => w t = x ∧ j t = r).card)

/-- PDF p.31: the conditional exact-type projector, with original time order restored. -/
def conditionalExactProjector {a d n : ℕ} (S : Fin a → FineResolution d) (w : Fin n → Fin a)
    (r : Fin a → Fin d → ℕ) :=
  ∑ j ∈ (Finset.univ.filter fun j : Fin n → Fin d => ∀ x k,
    (Finset.univ.filter fun t => w t = x ∧ j t = k).card = r x k),
    wordTensor (fun t => (S (w t)).atom (j t))

/-- PDF p.31: a realizable conditional type's comparison states. An empty input
class is assigned the original state; its entropy/divergence weight is exactly zero. -/
def conditionalTypeState {a d n : ℕ} (S : Fin a → FineResolution d) (w : Fin n → Fin a)
    (r : Fin a → Fin d → ℕ) (x : Fin a) : Matrix (Fin d) (Fin d) ℂ :=
  if count w x = 0 then (S x).state else
    ∑ j, ((r x j / (count w x : ℝ) : ℝ) : ℂ) • (S x).atom j

/-- PDF p.31: conditional entropy-low projector, as a finite sum of realizable types. -/
def lowConditionalProjector {a d n : ℕ} (S : Fin a → FineResolution d) (w : Fin n → Fin a) (L : ℝ) :=
  ∑ r ∈ ((conditionalTypes d w).filter fun r =>
      (∑ x, empiricalWeight w x * vnEntropy (conditionalTypeState S w r x)) ≤ L),
    conditionalExactProjector S w r

/-- PDF p.31: low-entropy divergence infimum for a single normalized state. -/
def lowEntropyDivergence {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (L : ℝ) : ℝ≥0∞ :=
  sInf {D | ∃ nu : Matrix I I ℂ, IsDensityMatrix nu ∧ vnEntropy nu ≤ L ∧ D = relativeBits nu rho}

/-- PDF pp.53-55: separate classical encoders and a collective conditioned POVM
on the free Y^n register, retaining an explicit failure outcome. -/
structure SideCode {s : ℕ} (S : HybridSource s) (n : ℕ) where
  length_pos : 0 < n
  messages : Fin s → ℕ
  messages_pos : ∀ i, 0 < messages i
  encode : ∀ i, (Fin n → Fin (S.alphabet i)) → Fin (messages i)
  decode : (∀ i, Fin (messages i)) →
    Option (∀ i, Fin n → Fin (S.alphabet i)) →
    Matrix (Fin n → Fin S.system.dim) (Fin n → Fin S.system.dim) ℂ
  povm : ∀ m, IsPOVM (decode m)
  blocks : ∀ m x, QAlgorithms.Papers.Independent.Claimed50.P40.InBlockPower S.system.block n (decode m x)

/-- PDF pp.53-55: classical words obtained from an iid joint source word. -/
def HybridSource.classicalWords {s n : ℕ} (S : HybridSource s)
    (w : Fin n → ((∀ i, Fin (S.alphabet i)) × Fin S.pure_count)) :=
  fun i t => (w t).1 i

/-- PDF pp.53-55: Y word, with the correct block power. -/
def HybridSource.sideWord {s n : ℕ} (S : HybridSource s)
    (w : Fin n → ((∀ i, Fin (S.alphabet i)) × Fin S.pure_count)) :=
  wordTensor (fun t => S.letter (w t).2)

/-- PDF pp.53-55: actual message tuple, each message seeing its own classical word only. -/
def SideCode.message {s n : ℕ} {S : HybridSource s} (c : SideCode S n)
    (x : ∀ i, Fin n → Fin (S.alphabet i)) := fun i => c.encode i (x i)

/-- PDF pp.53-55: ensemble-averaged whole-tuple decoding error. -/
def SideCode.error {s n : ℕ} {S : HybridSource s} (c : SideCode S n) : ℝ :=
  1 - ∑ w : Fin n → ((∀ i, Fin (S.alphabet i)) × Fin S.pure_count),
    (∏ t, (S.law (w t)).toReal) * effectProb (S.sideWord w)
      (c.decode (c.message (S.classicalWords w)) (some (S.classicalWords w)))

/-- PDF pp.53-55: mean unhalved trace norm for the actual labelled square-root
instrument after discarding transmitted classical messages, including its failure block. -/
def SideCode.disturbance {s n : ℕ} {S : HybridSource s} (c : SideCode S n) : ℝ :=
  ∑ w : Fin n → ((∀ i, Fin (S.alphabet i)) × Fin S.pure_count),
    (∏ t, (S.law (w t)).toReal) *
      totalDisturbance (c.decode (c.message (S.classicalWords w))) (S.sideWord w)
        (some (S.classicalWords w))

/-- PDF pp.53-55: classical message rate in bits per source symbol. -/
def SideCode.rate {s n : ℕ} {S : HybridSource s} (c : SideCode S n) (i : Fin s) : ℝ :=
  Real.logb 2 (c.messages i) / n

/-- PDF p.54: marginal probability of a classical tuple. -/
def HybridSource.classicalMass {s : ℕ} (S : HybridSource s) (x : ∀ i, Fin (S.alphabet i)) : ℝ :=
  ∑ p, (S.law (x,p)).toReal

/-- PDF p.54: conditional Y state. A zero-mass branch is filled by a fixed source
pure state, rather than by an unnormalized zero state. -/
def HybridSource.conditional {s : ℕ} (S : HybridSource s) (x : ∀ i, Fin (S.alphabet i)) :=
  if S.classicalMass x = 0 then S.letter ⟨0,S.pure_count_pos⟩ else
    ∑ p, (((S.law (x,p)).toReal / S.classicalMass x : ℝ) : ℂ) • S.letter p

/-- PDF pp.56-57: quantum source encoder with classical side information. The
`encoderKnows` flag changes its actual domain: false requires one common encoding
for every classical word; the decoder always receives the classical word for free. -/
structure ClassicalSideCode (S : HybridSource 1) (n : ℕ) (encoderKnows : Bool) where
  length_pos : 0 < n
  dim : ℕ
  dim_pos : 0 < dim
  encode : (Fin n → Fin (S.alphabet 0)) → (Fin n → Fin S.pure_count) →
    Matrix (Fin dim) (Fin dim) ℂ
  encoded_state : ∀ x p, IsDensityMatrix (encode x p)
  decoderOnly : encoderKnows = false → ∀ x y p, encode x p = encode y p
  decode : (Fin n → Fin (S.alphabet 0)) → Superop (Fin dim) (Fin n → Fin S.system.dim)
  decoder_channel : ∀ x, IsChannel (decode x)

/-- PDF pp.56-57: actual ensemble-averaged pure-word fidelity. -/
def ClassicalSideCode.fidelity {S : HybridSource 1} {n : ℕ} {known : Bool}
    (c : ClassicalSideCode S n known) : ℝ :=
  ∑ w : Fin n → ((∀ i, Fin (S.alphabet i)) × Fin S.pure_count),
    (∏ t, (S.law (w t)).toReal) *
      effectProb (c.decode (fun t => (w t).1 0)
        (c.encode (fun t => (w t).1 0) (fun t => (w t).2))) (S.sideWord w)

/-- PDF p.57: fixed-error limsup of operational minimum rates, with the encoder's
side-information domain part of the code type. -/
def classicalSideRate (S : HybridSource 1) (encoderKnows : Bool) (lambda : ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun n : ℕ => sInf {r |
    ∃ c : ClassicalSideCode S (n+1) encoderKnows, 1 - c.fidelity ≤ lambda ∧
      r = ENNReal.ofReal (Real.logb 2 c.dim / (n+1 : ℝ))}) atTop

/-- PDF pp.40,43: the independent sender law, constructed before the pure
conditional-output refinement. The product normalization is a finite distributive law. -/
def independentLaw {s : ℕ} {a : Fin s → ℕ} (P : ∀ i, PMF (Fin (a i))) :
    PMF (∀ i, Fin (a i)) :=
  PMF.ofFintype (fun x => ∏ i, P i (x i)) (by
    rw [← Fintype.prod_sum]
    have h : ∀ i, (∑ x, P i x) = 1 := fun i => by simpa only [tsum_fintype] using (P i).tsum_coe
    simp only [h, Finset.prod_const_one])

/-- PDF p.43: source reduction data, with the source constructed from normalized
pure decompositions of EVERY channel output and the independent sender laws. -/
def macReductionSource
    (C : QAlgorithms.Papers.Independent.Claimed50.P40.ClassicalChannel 2)
    (P : QAlgorithms.Papers.Independent.Claimed50.P40.InputLaw C.alphabet)
    (b : ℕ) (hb : 0 < b) (pi : Fin b → Matrix (Fin C.output) (Fin C.output) ℂ)
    (hpure : ∀ j, (IsPure (pi j)) ∧ InBlocks C.block (pi j)) (hdistinct : Function.Injective pi)
    (q : (∀ i, Fin (C.alphabet i)) → PMF (Fin b)) : HybridSource 2 where
  alphabet := C.alphabet
  alphabet_pos := C.alphabet_pos
  system := ⟨C.output, C.output_pos, C.block⟩
  pure_count := b
  pure_count_pos := hb
  letter := pi
  pure := hpure
  distinct := hdistinct
  law := (independentLaw P).bind (fun x => PMF.map (fun j => (x,j)) (q x))

/-- Empty temporal block is the scalar identity, even for entangled source letters. -/
example {s : ℕ} {L : Type*} [Fintype L] (S : MultipleData s L) (w : Fin 0 → L)
    (a b : PartyWords S.system 0) : S.word w a b = 1 := by
  simp [MultipleData.word]

/-- Independent-law construction retains the actual product weights. -/
example {s : ℕ} {a : Fin s → ℕ} (P : ∀ i, PMF (Fin (a i))) (x : ∀ i, Fin (a i)) :
    independentLaw P x = ∏ i, P i (x i) := rfl

end QAlgorithms.Papers.Independent.Renew46.P43


