-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04
-- name    : QAlgorithms_Papers_Independent_Support50_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T18:25:47.893979+00:00
-- url     : https://prove2.me/theorems/6b63f3ef-3ea7-4347-802c-42a76aa72061
-- title:
--   Definitions for Quantum Coding with Finite Resources
-- statement:
--   The objects the formalized statements of *Quantum Coding with Finite Resources* (arXiv:1504.04617) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `sourcePurification`: PDF p.8: source purification has coefficients sqrt(rho)[i,j], with the square root on the FIRST factor. Its first marginal is rho; no full-rank assumption is imposed.
--   - `sourcePurifiedOutput`: PDF p.9, Eq.(21): actual purified channel output in reference:receiver order.
--   - `localEmbedding`: PDF p.10: embed Alice and Bob separately into fixed larger local registers. The product embedding introduces only local pure ancillas, with no shared resource.
--   - `pairConfiguration`: PDF p.10: dependent two-party coordinates, with potentially UNEQUAL local dimensions.
--   - `receiverConfigurationMarginal`: PDF p.10: read the receiver register after an LOCC map on two enlarged local registers.
--   - `IsReceiverLOCC`: PDF p.10, Fig.5: an LOCC decoder with output at Bob. The accepted InLOCC predicate requires linked actual local instruments, rather than independently approximating finite protocols (the larger closure). Ancilla embeddings and final local disposal are explicit. All local dimensions are finite and positive.
--   - `CppCode`: PDF p.10: cpp entanglement transmission, for one (possibly blocked) channel. The encoder retains finite sender memory; the only communication after channel uses is LOCC. No preshared entanglement is an input field.
--   - `cppEffective`: PDF p.10: apply N to the channel input, preserve memory, then decode at Bob.
--   - `cppFidelity`: PDF pp.2,8,10: squared fidelity to normalized Phi_M of the actual cpp output.
--   - `unassistedFeasible`: PDF pp.2–3: exact finite-block unassisted feasibility with positive INTEGER messages.
--   - `cppFeasible`: PDF pp.3,10: exact cpp finite-block feasibility, not feasibility in a closure of codes.
--   - `unassistedBoundary`: PDF p.3, Eq.(2): per-use rate boundary. Extrema are extended before optimization. For n>=1, CPTP N on positive finite systems and epsilon<1, feasible integer message sizes are nonempty and bounded, so this is the source's attained maximum rate.
--   - `cppBoundary`: PDF pp.3,10: cpp boundary over actual feasible codes. Same finite-integer maximum convention as unassistedBoundary; a supremum of fidelity is not substituted for feasibility.
--   - `optimalCppFidelity`: PDF pp.5,18: fixed-message optimal cpp fidelity; the exact erasure theorem also asserts attainment by an actual code. Positive M is a theorem hypothesis.
--   - `binaryVariance`: PDF p.4: binary information variance in bits squared, including zero dispersion.
--   - `normalRate`: PDF pp.3,8: normal approximation per use, with standard Gaussian quantile.
--   - `thirdOrderExpansion`: PDF p.4, Eq.(6): two-sided eventual O(1/n), constants fixed before n.
--   - `constantRemainderExpansion`: PDF p.6, Eq.(9): two-sided O(1/n), with no log(n)/n third-order term.
--   - `dispersionUpper`: PDF pp.7,13: one-sided converse with an eventual O(log n/n) remainder.
--   - `dispersionLower`: PDF pp.8,14: one-sided achievability; this does not assert a two-sided expansion.
--   - `channelTestingRains`: PDF p.9, Eq.(21): sup over input states BEFORE the statewise inf over PPT-prime.
--   - `FullUnitaryCovariant`: PDF pp.12–13: full input-unitary covariance, with an output unitary representation. This is not arbitrary-group or trivial-group covariance.
--   - `choiState`: PDF p.8: normalized Choi state, as distinct from the unnormalized SDP Choi matrix.
--   - `rainsInformation`: PDF p.13, Eq.(41): Rains information at the constructed maximally entangled input.
--   - `rainsOptimizers`: PDF p.13: ALL actual Rains minimizers, not freely supplied optimization data.
--   - `rainsVariance`: PDF p.13, Eq.(42): maximum below epsilon=1/2; minimum at or above it.
--   - `channelCoherentBits`: PDF p.14, Eq.(48): optimized coherent information, in bits, over ALL density inputs.
--   - `coherentOptimizers`: PDF p.14: constructed coherent-information maximizing inputs, including rank-deficient ones.
--   - `coherentInformationVariance`: PDF p.14, Eq.(49): minimum variance below epsilon=1/2; maximum at or above it.
--   - `smoothMinEntropy`: PDF pp.13–14, Eq.(44), corrected named purified-distance ball: F>=1-delta^2. The exponent supremum is extended first; zero subnormalized states have infinite min-entropy, but are excluded by this ball at normalized center and delta<1.
--   - `smoothInner`: PDF p.14, Eq.(46): optimized blocked smooth-entropy inner bound, including rounding.
--   - `productSmoothInner`: PDF p.14, Eq.(47): eta=1/sqrt(n), with the square root applied AFTER subtraction. The theorem requires 1/sqrt(n)<epsilon, correcting the printed domain.
--   - `erasureFidelityFormula`: PDF p.18, Eqs.(69)–(70): exact fixed-integer-message fidelity, with all erasure counts. Since l<=n, n-l never truncates an intended negative number; M is positive in results.
--   - `dephasingAlternative`: PDF p.16, Eq.(61): fixed dephasing testing pair.
--   - `depolarizingAlternative`: PDF p.19, Eq.(73): Bell weights (1/2,1/6,1/6,1/6), a normalized PPT alternative.
--   - `bscJoint`: PDF p.16, Eq.(63): the BSC joint law, uniform input; comparison law is uniform on pairs.
--   - `bscAlternative`: PDF p.16: fixed product of uniform binary marginals.
--   - `PptChoiTP`: PDF pp.9,12: comparison-channel Choi operators are PSD, PPT, and trace preserving.
--   - `PptChoiTNI`: PDF pp.21–22: the appendix uses trace-NONINCREASING comparison maps. For PSD tests this has the same supremum, by product-PPT completion of the deficit.
--   - `GammaTests`: PDF p.12, Eq.(33): Gamma constraints with Loewner, not entrywise, inequalities.
--   - `comparisonValue`: PDF p.12, Eq.(33): inner supremum over actual PPT-binding channel Choi matrices.
--   - `metaValue`: PDF p.12, Eq.(33): inf_rho inf_Lambda sup_PPT in exactly that order. The feasible pair set is nonempty for CPTP N and epsilon in (0,1); objective lies in [0,1].
--   - `SdpMinFeasible`: PDF p.21, Eq.(A3): full minimization feasibility, with all identity tensor factors.
--   - `sdpMinValue`: PDF p.21, Eq.(A3): infimum of the trace objective over the constructed program.
--   - `SdpMaxFeasible`: PDF pp.21–22, Eq.(A4): scalar nu consistently replaces the printed n/nu typo. Tr_B R<=nu I is equivalent under transpose to Tr_B(R^{T_A})<=nu I.
--   - `sdpMaxValue`: PDF p.21, Eq.(A4): the dual supremum, not an assumed optimization value.
--   - `BinaryWord`: PDF p.16: binary vectors with the field addition used in parity checks.
--   - `xKet`: PDF p.16: Fourier-character ket |c>_X in the physical Z basis.
--   - `cssIsometry`: PDF pp.16–17: the CSS encoder sends message m to the X-basis word indexed by c_m.
--   - `syndromeProjector`: PDF p.17: the syndrome-s projector, retaining EVERY syndrome outcome.
--   - `zError`: PDF p.17: correction Z^u is diagonal with signs (-1)^(u dot z).
--   - `cssDecoder`: PDF p.17: explicit syndrome measurement, phase correction, and inverse CSS isometry.
--   - `phaseErrorProbability`: PDF pp.16–17: independent phase-error law, including endpoint probabilities.
--   - `classicalLinearSuccess`: PDF p.16: actual uniform-message average success for the syndrome decoder. The received word is c_m+u, and decoding subtracts the estimated error.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, https://arxiv.org/abs/1504.04617v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

/-!
Statements from Quantum Coding with Finite Resources, arXiv:1504.04617v2.
All newly introduced objects are confined to this paper. Operational extrema use
EReal before optimization. Explicit source corrections are recorded in the unit's
MODERATION_NOTES.md; source-domain deferrals are in HARD.md. Compilation pending.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- PDF p.8: source purification has coefficients sqrt(rho)[i,j], with the square root
on the FIRST factor. Its first marginal is rho; no full-rank assumption is imposed. -/
def sourcePurification (rho : Matrix A A ℂ) : Matrix (A × A) (A × A) ℂ :=
  let S := cfc Real.sqrt rho
  fun p q => S p.1 p.2 * conj (S q.1 q.2)

/-- PDF p.9, Eq.(21): actual purified channel output in reference:receiver order. -/
def sourcePurifiedOutput (N : Superop A B) (rho : Matrix A A ℂ) :
    Matrix (A × B) (A × B) ℂ := idTensorSuperop N (sourcePurification rho)

/-- PDF p.10: embed Alice and Bob separately into fixed larger local registers.
The product embedding introduces only local pure ancillas, with no shared resource. -/
def localEmbedding {Q T : Type} [Fintype Q] [Fintype T] {a b : ℕ}
    (W : Matrix (Fin a) Q ℂ) (V : Matrix (Fin b) T ℂ) :
    Matrix (QAlgorithms.Papers.Independent.Information100.P27.Config ![a,b]) (Q × T) ℂ :=
  fun x y => W (x 0) y.1 * V (x 1) y.2

/-- PDF p.10: dependent two-party coordinates, with potentially UNEQUAL local dimensions. -/
def pairConfiguration {a b : ℕ} (i : Fin a) (j : Fin b) :
    QAlgorithms.Papers.Independent.Information100.P27.Config ![a,b] :=
  Fin.cases i (Fin.cases j (fun k => Fin.elim0 k))

/-- PDF p.10: read the receiver register after an LOCC map on two enlarged local registers. -/
def receiverConfigurationMarginal {a b : ℕ}
    (X : Matrix (QAlgorithms.Papers.Independent.Information100.P27.Config ![a,b])
      (QAlgorithms.Papers.Independent.Information100.P27.Config ![a,b]) ℂ) :
    Matrix (Fin b) (Fin b) ℂ :=
  fun j k => ∑ i : Fin a, X (pairConfiguration i j) (pairConfiguration i k)

/-- PDF p.10, Fig.5: an LOCC decoder with output at Bob. The accepted InLOCC
predicate requires linked actual local instruments, rather than independently
approximating finite protocols (the larger closure). Ancilla embeddings and final
local disposal are explicit. All local dimensions are finite and positive. -/
def IsReceiverLOCC {Q T : Type} [Fintype Q] [DecidableEq Q]
    [Fintype T] [DecidableEq T] {M : ℕ} (D : Superop (Q × T) (Fin M)) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    ∃ W : Matrix (Fin a) Q ℂ, ∃ V : Matrix (Fin b) T ℂ,
    Wᴴ * W = 1 ∧ Vᴴ * V = 1 ∧
    ∃ L : Superop (QAlgorithms.Papers.Independent.Information100.P27.Config ![a,b])
      (QAlgorithms.Papers.Independent.Information100.P27.Config ![a,b]),
    QAlgorithms.Papers.Independent.Dependency50.P22.InLOCC ![a,b] (fun _ : Unit => L) ∧
    ∃ F : Superop (Fin b) (Fin M), IsChannel F ∧
      ∀ X, D X = F (receiverConfigurationMarginal (L (conjSuperop (localEmbedding W V) X)))

/-- PDF p.10: cpp entanglement transmission, for one (possibly blocked) channel.
The encoder retains finite sender memory; the only communication after channel
uses is LOCC. No preshared entanglement is an input field. -/
structure CppCode (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] where
  M : ℕ
  positive : 0 < M
  q : ℕ
  memory_positive : 0 < q
  encoder : Superop (Fin M) (A × Fin q)
  encoder_channel : IsChannel encoder
  decoder : Superop (Fin q × B) (Fin M)
  decoder_channel : IsChannel decoder
  decoder_locc : IsReceiverLOCC decoder

/-- PDF p.10: apply N to the channel input, preserve memory, then decode at Bob. -/
def cppEffective (N : Superop A B) (C : CppCode A B) : Superop (Fin C.M) (Fin C.M) :=
  fun X => C.decoder (idTensorSuperop (R := Fin C.q) N
    (fun p q => C.encoder X (p.2,p.1) (q.2,q.1)))

/-- PDF pp.2,8,10: squared fidelity to normalized Phi_M of the actual cpp output. -/
def cppFidelity (N : Superop A B) (C : CppCode A B) : ℝ :=
  effectProb (QAlgorithms.Papers.Independent.Dependency50.P36.target C.M) (idTensorSuperop (cppEffective N C) (QAlgorithms.Papers.Independent.Dependency50.P36.target C.M))

/-- PDF pp.2–3: exact finite-block unassisted feasibility with positive INTEGER messages. -/
def unassistedFeasible (N : Superop A B) (n : ℕ) (epsilon R : ℝ) : Prop :=
  ∃ C : QAlgorithms.Papers.Independent.Information100.P80.TransmissionCode (Fin n → A) (Fin n → B),
    R ≤ QAlgorithms.Papers.Independent.Information100.P80.log2 C.M / n ∧ 1 - epsilon ≤ QAlgorithms.Papers.Independent.Information100.P80.transmissionFidelity (piSuperop (fun _ : Fin n => N)) C

/-- PDF pp.3,10: exact cpp finite-block feasibility, not feasibility in a closure of codes. -/
def cppFeasible (N : Superop A B) (n : ℕ) (epsilon R : ℝ) : Prop :=
  ∃ C : CppCode (Fin n → A) (Fin n → B),
    R ≤ QAlgorithms.Papers.Independent.Information100.P80.log2 C.M / n ∧ 1 - epsilon ≤ cppFidelity (piSuperop (fun _ : Fin n => N)) C

/-- PDF p.3, Eq.(2): per-use rate boundary. Extrema are extended before optimization.
For n>=1, CPTP N on positive finite systems and epsilon<1, feasible integer message
sizes are nonempty and bounded, so this is the source's attained maximum rate. -/
def unassistedBoundary (N : Superop A B) (n : ℕ) (epsilon : ℝ) : EReal :=
  sSup {r | ∃ R : ℝ, unassistedFeasible N n epsilon R ∧ r = (R : EReal)}

/-- PDF pp.3,10: cpp boundary over actual feasible codes. Same finite-integer maximum
convention as unassistedBoundary; a supremum of fidelity is not substituted for feasibility. -/
def cppBoundary (N : Superop A B) (n : ℕ) (epsilon : ℝ) : EReal :=
  sSup {r | ∃ R : ℝ, cppFeasible N n epsilon R ∧ r = (R : EReal)}

/-- PDF pp.5,18: fixed-message optimal cpp fidelity; the exact erasure theorem also
asserts attainment by an actual code. Positive M is a theorem hypothesis. -/
def optimalCppFidelity (N : Superop A B) (n M : ℕ) : EReal :=
  sSup {f | ∃ C : CppCode (Fin n → A) (Fin n → B), C.M = M ∧
    f = (cppFidelity (piSuperop (fun _ : Fin n => N)) C : EReal)}

/-- PDF p.4: binary information variance in bits squared, including zero dispersion. -/
def binaryVariance (p : ℝ) : ℝ :=
  p * (QAlgorithms.Papers.Independent.Information100.P80.log2 p + QAlgorithms.Papers.Independent.Frontier18.P07.binaryEntropyBits p)^2 +
    (1-p) * (QAlgorithms.Papers.Independent.Information100.P80.log2 (1-p) + QAlgorithms.Papers.Independent.Frontier18.P07.binaryEntropyBits p)^2

/-- PDF pp.3,8: normal approximation per use, with standard Gaussian quantile. -/
def normalRate (a v epsilon : ℝ) (n : ℕ) : ℝ :=
  a + Real.sqrt (v / n) * QAlgorithms.Papers.Independent.Information100.P63.normalQuantile epsilon

/-- PDF p.4, Eq.(6): two-sided eventual O(1/n), constants fixed before n. -/
def thirdOrderExpansion (R : ℕ → EReal) (a v epsilon : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
    let t := normalRate a v epsilon n + QAlgorithms.Papers.Independent.Information100.P80.log2 n / (2*n)
    ((t - C/n : ℝ) : EReal) ≤ R n ∧ R n ≤ ((t + C/n : ℝ) : EReal)

/-- PDF p.6, Eq.(9): two-sided O(1/n), with no log(n)/n third-order term. -/
def constantRemainderExpansion (R : ℕ → EReal) (a v epsilon : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
    ((normalRate a v epsilon n - C/n : ℝ) : EReal) ≤ R n ∧
    R n ≤ ((normalRate a v epsilon n + C/n : ℝ) : EReal)

/-- PDF pp.7,13: one-sided converse with an eventual O(log n/n) remainder. -/
def dispersionUpper (R : ℕ → EReal) (a v epsilon : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
    R n ≤ ((normalRate a v epsilon n + C * QAlgorithms.Papers.Independent.Information100.P80.log2 n / n : ℝ) : EReal)

/-- PDF pp.8,14: one-sided achievability; this does not assert a two-sided expansion. -/
def dispersionLower (R : ℕ → EReal) (a v epsilon : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
    ((normalRate a v epsilon n - C * QAlgorithms.Papers.Independent.Information100.P80.log2 n / n : ℝ) : EReal) ≤ R n

/-- PDF p.9, Eq.(21): sup over input states BEFORE the statewise inf over PPT-prime. -/
def channelTestingRains (N : Superop A B) (epsilon : ℝ) : EReal :=
  sSup {r | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
    r = sInf {d | ∃ sigma : Matrix (A × B) (A × B) ℂ,
      QAlgorithms.Papers.Independent.Dependency50.P36.pptPrime sigma ∧ d = QAlgorithms.Papers.Independent.Dependency50.P36.testingEntropy (sourcePurifiedOutput N rho) sigma epsilon}}

/-- PDF pp.12–13: full input-unitary covariance, with an output unitary representation.
This is not arbitrary-group or trivial-group covariance. -/
def FullUnitaryCovariant (N : Superop A B) : Prop :=
  ∃ V : Matrix.unitaryGroup A ℂ →* Matrix.unitaryGroup B ℂ,
    ∀ U : Matrix.unitaryGroup A ℂ, ∀ X,
      N (conjSuperop (U : Matrix A A ℂ) X) =
        conjSuperop (V U : Matrix B B ℂ) (N X)

/-- PDF p.8: normalized Choi state, as distinct from the unnormalized SDP Choi matrix. -/
def choiState (N : Superop A B) : Matrix (A × B) (A × B) ℂ :=
  ((Fintype.card A : ℂ)⁻¹) • QAlgorithms.Papers.Independent.Information100.P34.choi N

/-- PDF p.13, Eq.(41): Rains information at the constructed maximally entangled input. -/
def rainsInformation (N : Superop A B) : EReal :=
  sInf {r | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    QAlgorithms.Papers.Independent.Dependency50.P36.pptPrime sigma ∧ r = QAlgorithms.Papers.Independent.Dependency50.P36.relativeEntropy (choiState N) sigma}

/-- PDF p.13: ALL actual Rains minimizers, not freely supplied optimization data. -/
def rainsOptimizers (N : Superop A B) : Set (Matrix (A × B) (A × B) ℂ) :=
  {sigma | QAlgorithms.Papers.Independent.Dependency50.P36.pptPrime sigma ∧
    QAlgorithms.Papers.Independent.Dependency50.P36.relativeEntropy (choiState N) sigma = rainsInformation N}

/-- PDF p.13, Eq.(42): maximum below epsilon=1/2; minimum at or above it. -/
def rainsVariance (N : Superop A B) (epsilon : ℝ) : ℝ :=
  let vs := {v | ∃ sigma ∈ rainsOptimizers N, v = QAlgorithms.Papers.Independent.Dependency50.P36.pairInformationVariance (choiState N) sigma}
  if epsilon < 1/2 then sSup vs else sInf vs

/-- PDF p.14, Eq.(48): optimized coherent information, in bits, over ALL density inputs. -/
def channelCoherentBits (N : Superop A B) : ℝ :=
  sSup {v | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
    v = QAlgorithms.Papers.Independent.Dependency50.P36.stateCoherentInformationBits (sourcePurifiedOutput N rho)}

/-- PDF p.14: constructed coherent-information maximizing inputs, including rank-deficient ones. -/
def coherentOptimizers (N : Superop A B) : Set (Matrix A A ℂ) :=
  {rho | IsDensityMatrix rho ∧ QAlgorithms.Papers.Independent.Dependency50.P36.stateCoherentInformationBits (sourcePurifiedOutput N rho) = channelCoherentBits N}

/-- PDF p.14, Eq.(49): minimum variance below epsilon=1/2; maximum at or above it. -/
def coherentInformationVariance (N : Superop A B) (epsilon : ℝ) : ℝ :=
  let vs := {v | ∃ rho ∈ coherentOptimizers N,
    v = QAlgorithms.Papers.Independent.Dependency50.P36.coherentVariance (sourcePurifiedOutput N rho)}
  if epsilon < 1/2 then sInf vs else sSup vs

/-- PDF pp.13–14, Eq.(44), corrected named purified-distance ball: F>=1-delta^2.
The exponent supremum is extended first; zero subnormalized states have infinite
min-entropy, but are excluded by this ball at normalized center and delta<1. -/
def smoothMinEntropy {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (delta : ℝ) : EReal :=
  sSup {h | ∃ tau : Matrix (I × J) (I × J) ℂ,
    tau.PosSemidef ∧ tau.trace.re ≤ 1 ∧
    1 - delta^2 ≤ rootFidelity tau rho ^ 2 ∧
    ∃ sigma : Matrix J J ℂ, IsDensityMatrix sigma ∧
    ∃ lambda : ℝ, h = (lambda : EReal) ∧
      ((Real.rpow 2 (-lambda) : ℂ) • Matrix.kronecker (1 : Matrix I I ℂ) sigma - tau).PosSemidef}

/-- PDF p.14, Eq.(46): optimized blocked smooth-entropy inner bound, including rounding. -/
def smoothInner (Nc : Superop A E) (n : ℕ) (epsilon : ℝ) : EReal :=
  sSup {v | ∃ eta : ℝ, 0 < eta ∧ eta < epsilon ∧
    ∃ rho : Matrix (Fin n → A) (Fin n → A) ℂ, IsDensityMatrix rho ∧
    v = (smoothMinEntropy (sourcePurifiedOutput (piSuperop (fun _ : Fin n => Nc)) rho) (Real.sqrt (epsilon-eta)) -
      ((4 * QAlgorithms.Papers.Independent.Information100.P80.log2 (1/eta) + 1 : ℝ) : EReal)) / (n : EReal)}

/-- PDF p.14, Eq.(47): eta=1/sqrt(n), with the square root applied AFTER subtraction.
The theorem requires 1/sqrt(n)<epsilon, correcting the printed domain. -/
def productSmoothInner (Nc : Superop A E) (n : ℕ) (epsilon : ℝ) : EReal :=
  sSup {v | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
    v = (smoothMinEntropy
      (QAlgorithms.Papers.Independent.Information100.P80.groupedPower (sourcePurifiedOutput Nc rho) n)
      (Real.sqrt (epsilon - 1/Real.sqrt n)) -
      ((2 * QAlgorithms.Papers.Independent.Information100.P80.log2 n + 1 : ℝ) : EReal)) / (n : EReal)}

/-- PDF p.18, Eqs.(69)–(70): exact fixed-integer-message fidelity, with all erasure counts.
Since l<=n, n-l never truncates an intended negative number; M is positive in results. -/
def erasureFidelityFormula (beta : ℝ) (n M : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (n+1), (n.choose l : ℝ) * beta^l * (1-beta)^(n-l) *
    min 1 ((2 : ℝ)^(n-l) / M)

/-- PDF p.16, Eq.(61): fixed dephasing testing pair. -/
def dephasingAlternative : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  choiState (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*(1/2)))

/-- PDF p.19, Eq.(73): Bell weights (1/2,1/6,1/6,1/6), a normalized PPT alternative. -/
def depolarizingAlternative : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  choiState (QuditFidelity.depolarizingMap 2 (by norm_num) (4*(1/2)/3))

/-- PDF p.16, Eq.(63): the BSC joint law, uniform input; comparison law is uniform on pairs. -/
def bscJoint (gamma : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal fun p => (if p.1 = p.2 then ((1-gamma)/2 : ℂ) else (gamma/2 : ℂ))

/-- PDF p.16: fixed product of uniform binary marginals. -/
def bscAlternative : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1/4 : ℂ) • 1

/-- PDF pp.9,12: comparison-channel Choi operators are PSD, PPT, and trace preserving. -/
def PptChoiTP (J : Matrix (A × B) (A × B) ℂ) : Prop :=
  J.PosSemidef ∧ (QAlgorithms.Entanglement.partialTransposeFirst J).PosSemidef ∧ traceRight J = 1

/-- PDF pp.21–22: the appendix uses trace-NONINCREASING comparison maps.
For PSD tests this has the same supremum, by product-PPT completion of the deficit. -/
def PptChoiTNI (J : Matrix (A × B) (A × B) ℂ) : Prop :=
  J.PosSemidef ∧ (QAlgorithms.Entanglement.partialTransposeFirst J).PosSemidef ∧ (1 - traceRight J).PosSemidef

/-- PDF p.12, Eq.(33): Gamma constraints with Loewner, not entrywise, inequalities. -/
def GammaTests (N : Superop A B) (epsilon : ℝ)
    (rho : Matrix A A ℂ) (Lambda : Matrix (A × B) (A × B) ℂ) : Prop :=
  Lambda.PosSemidef ∧
    (Matrix.kronecker rho.transpose (1 : Matrix B B ℂ) - Lambda).PosSemidef ∧
    1 - epsilon ≤ (Lambda * QAlgorithms.Papers.Independent.Information100.P34.choi N).trace.re

/-- PDF p.12, Eq.(33): inner supremum over actual PPT-binding channel Choi matrices. -/
def comparisonValue (Lambda : Matrix (A × B) (A × B) ℂ) (tni : Bool) : ℝ :=
  sSup {v | ∃ J : Matrix (A × B) (A × B) ℂ,
    (if tni then PptChoiTNI J else PptChoiTP J) ∧ v = (Lambda * J).trace.re}

/-- PDF p.12, Eq.(33): inf_rho inf_Lambda sup_PPT in exactly that order.
The feasible pair set is nonempty for CPTP N and epsilon in (0,1); objective lies in [0,1]. -/
def metaValue (N : Superop A B) (epsilon : ℝ) (tni : Bool := false) : ℝ :=
  sInf {v | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
    ∃ Lambda : Matrix (A × B) (A × B) ℂ,
    GammaTests N epsilon rho Lambda ∧ v = comparisonValue Lambda tni}

/-- PDF p.21, Eq.(A3): full minimization feasibility, with all identity tensor factors. -/
def SdpMinFeasible (N : Superop A B) (epsilon : ℝ)
    (rho xi : Matrix A A ℂ) (Lambda Theta : Matrix (A × B) (A × B) ℂ) : Prop :=
  IsDensityMatrix rho ∧ GammaTests N epsilon rho Lambda ∧
    xi.PosSemidef ∧ Theta.PosSemidef ∧
    (Matrix.kronecker xi (1 : Matrix B B ℂ) - Lambda - QAlgorithms.Entanglement.partialTransposeFirst Theta).PosSemidef

/-- PDF p.21, Eq.(A3): infimum of the trace objective over the constructed program. -/
def sdpMinValue (N : Superop A B) (epsilon : ℝ) : ℝ :=
  sInf {v | ∃ rho xi : Matrix A A ℂ,
    ∃ Lambda Theta : Matrix (A × B) (A × B) ℂ,
    SdpMinFeasible N epsilon rho xi Lambda Theta ∧ v = xi.trace.re}

/-- PDF pp.21–22, Eq.(A4): scalar nu consistently replaces the printed n/nu typo.
Tr_B R<=nu I is equivalent under transpose to Tr_B(R^{T_A})<=nu I. -/
def SdpMaxFeasible (N : Superop A B) (mu nu : ℝ)
    (J R : Matrix (A × B) (A × B) ℂ) : Prop :=
  0 ≤ mu ∧ 0 ≤ nu ∧ PptChoiTNI J ∧ R.PosSemidef ∧
    (J + R - (mu : ℂ) • QAlgorithms.Papers.Independent.Information100.P34.choi N).PosSemidef ∧
    ((nu : ℂ) • (1 : Matrix A A ℂ) - traceRight R).PosSemidef

/-- PDF p.21, Eq.(A4): the dual supremum, not an assumed optimization value. -/
def sdpMaxValue (N : Superop A B) (epsilon : ℝ) : ℝ :=
  sSup {v | ∃ mu nu : ℝ, ∃ J R : Matrix (A × B) (A × B) ℂ,
    SdpMaxFeasible N mu nu J R ∧ v = mu * (1-epsilon) - nu}

/-- PDF p.16: binary vectors with the field addition used in parity checks. -/
abbrev BinaryWord (n : ℕ) := Fin n → ZMod 2

/-- PDF p.16: Fourier-character ket |c>_X in the physical Z basis. -/
def xKet {n : ℕ} (c : BinaryWord n) : EuclideanSpace ℂ (Fin n → Fin 2) :=
  WithLp.toLp 2 fun z => ((Real.sqrt ((2 : ℝ)^n))⁻¹ : ℂ) *
    (-1 : ℂ) ^ (∑ i, (c i).val * (z i).val)

/-- PDF pp.16–17: the CSS encoder sends message m to the X-basis word indexed by c_m. -/
def cssIsometry {n k : ℕ} (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) :
    Matrix (Fin n → Fin 2) (Fin (2^k)) ℂ :=
  fun z m => xKet (word ((Fintype.equivFin (BinaryWord k)).symm
    (Fin.cast (by simp [BinaryWord]) m))) z

/-- PDF p.17: the syndrome-s projector, retaining EVERY syndrome outcome. -/
def syndromeProjector {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (s : BinaryWord (n-k)) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ c : BinaryWord n, if H c = s then pureDensity (xKet c) else 0

/-- PDF p.17: correction Z^u is diagonal with signs (-1)^(u dot z). -/
def zError {n : ℕ} (u : BinaryWord n) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.diagonal fun z => (-1 : ℂ) ^ (∑ i, (u i).val * (z i).val)

/-- PDF p.17: explicit syndrome measurement, phase correction, and inverse CSS isometry. -/
def cssDecoder {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (estimate : BinaryWord (n-k) → BinaryWord n) :
    Superop (Fin n → Fin 2) (Fin (2^k)) :=
  krausApply fun s : BinaryWord (n-k) =>
    (cssIsometry word)ᴴ * zError (estimate s) * syndromeProjector H s

/-- PDF pp.16–17: independent phase-error law, including endpoint probabilities. -/
def phaseErrorProbability {n : ℕ} (gamma : ℝ) (u : BinaryWord n) : ℝ :=
  ∏ i, if u i = 0 then 1-gamma else gamma

/-- PDF p.16: actual uniform-message average success for the syndrome decoder.
The received word is c_m+u, and decoding subtracts the estimated error. -/
def classicalLinearSuccess {n k : ℕ} (gamma : ℝ)
    (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k)) (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n)
    (estimate : BinaryWord (n-k) → BinaryWord n) : ℝ :=
  ((2 : ℝ)^k)⁻¹ * ∑ m : BinaryWord k, ∑ u : BinaryWord n,
    if word m + u - estimate (H (word m + u)) = word m
    then phaseErrorProbability gamma u else 0

/-! Sanity examples pin the source conventions, without proving the target results. -/

example (M : ℕ) (x y : Fin M) : QAlgorithms.Papers.Independent.Dependency50.P36.target M (x,x) (y,y) = (M : ℂ)⁻¹ := by
  simp [QAlgorithms.Papers.Independent.Dependency50.P36.target]

example (rho : Matrix A A ℂ) (i j k l : A) :
    sourcePurification rho (i,j) (k,l) =
      (cfc Real.sqrt rho) i j * conj ((cfc Real.sqrt rho) k l) := rfl

example (X : Matrix (A × B) (A × B) ℂ) (i k : A) (j l : B) :
    QAlgorithms.Entanglement.partialTransposeFirst X (i,j) (k,l) = X (k,j) (i,l) := rfl

example : QAlgorithms.Papers.Independent.Frontier18.P07.binaryEntropyBits 0 = 0 ∧ binaryVariance 0 = 0 := by
  norm_num [QAlgorithms.Papers.Independent.Frontier18.P07.binaryEntropyBits, binaryVariance, QAlgorithms.Papers.Independent.Information100.P80.log2]

example (gamma : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma) X 0 1 = ((1-2*gamma : ℝ) : ℂ) * X 0 1 := by
  simp [QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing]

example (beta : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    QAlgorithms.Papers.Independent.Renew46.P36.flaggedErasure (A := Fin 2) beta X none none = (beta : ℂ) * X.trace := rfl

example (X : Matrix A A ℂ) : QAlgorithms.Papers.Independent.Information100.P60.copies 0 X = 1 := by
  ext x y
  simp [QAlgorithms.Papers.Independent.Information100.P60.copies, Matrix.one_apply, Subsingleton.elim x y]

example {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (estimate : BinaryWord (n-k) → BinaryWord n) :
    cssDecoder H word estimate = krausApply (fun s : BinaryWord (n-k) =>
      (cssIsometry word)ᴴ * zError (estimate s) * syndromeProjector H s) := rfl

/-- PDF p.8: a dimension-one target is the unit scalar density. -/
example : QAlgorithms.Papers.Independent.Dependency50.P36.target 1 (0,0) (0,0) = 1 := by norm_num [QAlgorithms.Papers.Independent.Dependency50.P36.target]

/-- PDF p.10: dependent coordinates retain the two unequal-dimensional local indices. -/
example {a b : ℕ} (i : Fin a) (j : Fin b) :
    pairConfiguration i j 0 = i ∧ pairConfiguration i j 1 = j := by
  constructor <;> rfl

/-- PDF p.10: channel noise acts on A and leaves the retained Q index unchanged. -/
example (N : Superop A B) (C : CppCode A B) (X : Matrix (Fin C.M) (Fin C.M) ℂ) :
    cppEffective N C X = C.decoder (idTensorSuperop (R := Fin C.q) N
      (fun p q => C.encoder X (p.2,p.1) (q.2,q.1))) := rfl

/-- PDF p.12: the test upper bound uses ordinary transpose on rho, not conjugate transpose. -/
example (N : Superop A B) (epsilon : ℝ) (rho : Matrix A A ℂ)
    (L : Matrix (A × B) (A × B) ℂ) (h : GammaTests N epsilon rho L) :
    (Matrix.kronecker rho.transpose (1 : Matrix B B ℂ) - L).PosSemidef := h.2.1

/-- PDF p.14: variance selection reverses between converse and achievability. -/
example (N : Superop A B) (epsilon : ℝ) (h : epsilon < 1/2) :
    coherentInformationVariance N epsilon = sInf
      {v | ∃ rho ∈ coherentOptimizers N,
        v = QAlgorithms.Papers.Independent.Dependency50.P36.coherentVariance (sourcePurifiedOutput N rho)} := by
  simp only [coherentInformationVariance, if_pos h]

/-- PDF p.18: no-use edge of the formula, outside theorem domain, has only l=0. -/
example (beta : ℝ) (M : ℕ) : erasureFidelityFormula beta 0 M = min 1 (1/(M : ℝ)) := by
  simp [erasureFidelityFormula]

/-- PDF pp.16–17: zero error pattern never changes a computational-basis phase. -/
example {n : ℕ} (z : Fin n → Fin 2) : zError (0 : BinaryWord n) z z = 1 := by
  simp [zError]

/-! One theorem for each nondeferred plan node. -/

end QAlgorithms.Papers.Independent.Support50.P04


