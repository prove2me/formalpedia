-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
-- name    : QAlgorithms_Papers_Independent_Information100_P67
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T12:48:55.918599+00:00
-- url     : https://prove2.me/theorems/534a8c71-b2cb-4172-af75-0a5de72756de
-- title:
--   Definitions for An exponential strong converse for private communication over degradable quantum channels
-- statement:
--   The objects the formalized statements of *An exponential strong converse for private communication over degradable quantum channels* (arXiv:2609.32515) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `squaredFidelity`: Squared algebraic fidelity, (2.1), PDF p.5. The frozen primitive is ROOT fidelity.
--   - `sineDistance`: Normalized-state sine distance, (2.2), PDF p.5.
--   - `IsIsometry`: Rectangular isometry; (2.6), PDF p.6.
--   - `receiverChannel`: Fixed-dilation receiver map, on ALL operators, (2.6), PDF p.6.
--   - `complementaryChannel`: Complement of precisely the same dilation, (2.6), PDF p.6.
--   - `IsDegradable`: Degrading direction, PDF p.6; Kraus normalization enforces CPTP.
--   - `IsAntidegradable`: Antidegrading direction, PDF p.6.
--   - `maximumCoherentInformation`: Maximum coherent information in bits, (2.7), PDF p.6. For an isometry on nonempty finite systems the set is nonempty and bounded; its supremum is attained.
--   - `dilationPower`: Tensor-power dilation, with all B and E factors grouped; (2.8), PDF p.6.
--   - `PrivateCode`: Raw data of an unassisted collective code, Section 2.1, PDF p.6. `Valid` below enforces normalization; no additional resources are fields.
--   - `PrivateCode.Valid`: Exactly the code assumptions of Section 2.1, PDF p.6.
--   - `messageOutput`: Messagewise estimate/environment state (2.8), PDF p.6. The POVM is applied to the B block of the ORIGINAL channel output.
--   - `jointOutput`: Uniform classical message prior, (2.9), PDF p.6.
--   - `idealJoint`: Mixed ideal classical key tensor a common environment state, (2.10), PDF p.7.
--   - `idealMessage`: Messagewise target; the same sigma is used for every m, (2.12), PDF p.7.
--   - `optimizedFidelity`: Optimized joint squared fidelity, (2.10), PDF p.7. On valid codes and isometric dilations the optimization is nonempty, bounded in [0,1], and attained.
--   - `environmentMarginal`: Actual environment marginal, (2.13), PDF p.7.
--   - `marginalFidelity`: Actual-marginal joint fidelity, (2.13), PDF p.7.
--   - `uniformError`: Uniform optimized infidelity, (2.11), PDF p.7.
--   - `marginalError`: Uniform actual-marginal infidelity, (2.13), PDF p.7.
--   - `maximalError`: Min_sigma max_message optimized infidelity, (2.14), PDF p.7. Validity ensures a nonempty message set and normalized-state optimization.
--   - `JointCriterion`: The three criteria of Section 2.1, PDF p.7.
--   - `codeError`: The named code error, PDF p.7.
--   - `AchievableRate`: Achievability (2.16), PDF p.7. Eventual lower bounds express the liminf rate. The n=0 term is immaterial to both limits.
--   - `privateCapacity`: Capacity as the supremum of ACHIEVABLE nonnegative rates, not a named coherent-information formula, PDF p.7. For finite nonempty physical systems and an isometry this set contains zero and is bounded above by log_2 dim B.
--   - `OptimizedDecay`: Uniform witnesses for an optimized strong converse above threshold q. Constants precede blocklength, messages, and every collective code (PDF pp.9,33).
--   - `decodingError`: Decoding error with the uniform prior, (D.10), PDF p.48.
--   - `secrecyError`: Trace-distance secrecy error with the actual marginal, (D.10), PDF p.48.
--   - `erasureDilation`: Literal orthogonal-flag erasure isometry, (7.10), PDF p.34. The receiver and complement have `Option A` basis (none is the flag).
--   - `privacyTest`: A privacy test from its diagonal twisting blocks, (3.3), PDF p.9. Only the mm blocks contribute; arbitrary off-diagonal blocks extend them. Tensor order is K,S,Khat,T. No separability is imposed on S,T.
--   - `decodedPrivacyTest`: Decode then test on the full receiver input, retaining its auxiliary, (3.18), PDF p.13. The map D changes only the receiver factor.
--   - `firstTest`: First projection on the common input KSXCYG1G2, (3.18), PDF p.13.
--   - `secondTest`: Second projection on the SAME space, identities on X,G1; (3.18), PDF p.13.
--   - `agreementCount`: Number of agreeing coordinates, (4.2), PDF p.17 (not Hamming distance).
--   - `uniformLabelMatrix`: Uniform label matrix 2^(-n) 11^T, PDF p.19.
--   - `binomialVolume`: Binomial SUM, not a single binomial coefficient; (4.12), PDF p.19.
--   - `IsSubnormalized`: Subnormalized PSD states, Appendix B.1, PDF p.42.
--   - `generalizedFidelity`: Generalized fidelity for subnormalized states, (B.1), PDF p.42.
--   - `purifiedDistance`: Purified distance on subnormalized states, (B.1), PDF p.42.
--   - `conditionalMaxEntropyValue`: Finite-real specialization of Hmax for NONZERO subnormalized rho, (B.3), PDF p.42. The log is outside the supremum of algebraic fidelities, which is positive for nonzero rho on positive-dimensional systems. At rho=0 this helper is unused (Hmax there is -infinity).
--   - `smoothConditionalMaxEntropy`: Real smooth Hmax at NORMALIZED center, 0≤epsilon<1, (B.4), PDF p.43. The ball contains subnormalized states. Zero is excluded explicitly because its distance from a normalized center is 1; it cannot be a feasible point. On this domain the nonempty entropy set is bounded above and below.
--   - `conditionalEntropy`: Conditional von Neumann entropy, (2.5), PDF p.6.
--   - `groupedPower`: Grouped tensor power of a bipartite matrix, PDF pp.30–31,43–45.
--   - `postselectionFactor`: Postselection scalar, (6.11)/(B.12), PDF pp.30,44.
--   - `entropyDimensionConstant`: Dimension-only AEP constant, (6.11), PDF p.30.
--   - `filterDimensionCorrection`: Recovery-error correction, (6.11)–(6.12), PDF p.30, defined explicitly for positive delta. No entropy theorem is a hidden input to this definition.
--   - `groupedChannelPower`: Group the output of T tensor n into F^n,E'^n, Appendix B.2, PDF p.43.
--   - `mapFirst`: Apply a channel to the FIRST factor, retaining the exact reference, used in (5.2), PDF p.24. Off-diagonal reference blocks are retained.
--   - `filteredKet`: The unnormalized linear-filter ket on the original state, (5.1), PDF p.24.
--   - `FilterGuarantee`: Single-filter recovery guarantee, (5.1)–(5.3), PDF p.24. No probability lower bound is imposed on the one selected filter.
--   - `gaussianFilterLaw`: Independent real standard Gaussians for real/imaginary matrix entries, (5.5), PDF p.25. The law is a finite product probability measure.
--   - `gaussianFilter`: Complex Gaussian matrix with E|Z_ai|^2=1/L, (5.5), PDF p.25.
--   - `referenceFilterMap`: CP (not necessarily TP) reference map Gamma_Z, (5.6), PDF p.25.
--   - `flaggedIdentityDilation`: Flagged identity dilation (D.9), PDF p.48: false is flag zero.
--   - `flaggedIdentityCode`: The explicit one-use code in Appendix D.2, PDF p.48. On flag one the reported message is the cyclic successor, irrespective of correctness.
--   - `flaggedExampleOutput`: The classical output (D.6), constructed from the flags, PDF p.48.
--   - `coherentCodeKet`: Canonical coherent ket (3.5)–(3.7), PDF pp.10–11. S=Kcopy×S1 and T=(Khatcopy×B^n)×Taux. Taux is local and starts in the basis ket `none`. All tensor permutations are explicit in the coordinate formula.
--   - `coherentClassicalMarginal`: Trace both shields out of a coherent ket, (3.8), PDF p.11.
--   - `swapReceiverCoordinate`: Exchange just coordinate j in two receiver copies, Section 4.1, PDF p.17.
--   - `symmetricReceiverMarginal`: Receiver marginal with one initialized local auxiliary, PDF pp.17–18. The other receiver copy is traced out; the sender shield is retained.
--   - `symmetricDilation`: Composed dilation, with tensor order F,(E',E), (6.1)–(6.2), PDF p.28.
--   - `IsSymmetricFactorization`: Basis-independent range form of the fixed symmetric factorization, (6.1)–(6.2), PDF p.28. The last equality is symmetry of the ISOMETRY, not merely equality of its two marginal channels.
--   - `environmentSwap`: Swap on the two identical environment factors, Appendix A, PDF pp.39–42.
--   - `mixedQubitExtension`: Independent receiver mixed qubit with its specified purification, Appendix A.2, PDF pp.41–42.
--   - `extendCode`: The corresponding original code, ignoring the appended receiver qubits, (A.13), PDF p.42. No input message state is changed.
--   - `symmetricEncoderOutput`: Coherent encoder output reordered as (F^n E'^n)(Rref E^n), (6.6), PDF p.29. Rref includes the sender key and shield in the code application.
--   - `conditionalMinEntropy`: Extended conditional min-entropy (B.2), PDF p.42. The real exponent set is embedded BEFORE taking the EReal supremum, preserving +infinity at zero.
--   - `conditionalMaxEntropy`: Extended conditional max-entropy (B.3), PDF p.42. The zero operator has value -infinity, rather than Real.logb's default value at zero.
--   - `smoothConditionalMinEntropy`: Extended smooth min-entropy on the full subnormalized ball, (B.4), PDF p.43.
--   - `smoothConditionalMaxEntropyExtended`: Extended smooth max-entropy on the full subnormalized ball, (B.4), PDF p.43. The real specialization above is used only at normalized centers and epsilon<1.
--   - `maximallyEntangledKey`: Entangled KEY KET (3.1), PDF p.9, distinct from the mixed ideal classical key used in the error criterion. Meaningful for M≥1.
--   - `idealClassicalKey`: Mixed uniform perfectly correlated classical key, (2.10), PDF p.7.
--   - `twistingUnitary`: Full controlled twisting unitary, (3.2), PDF p.9. Each block must be unitary in uses of this definition; off-diagonal key blocks are unrestricted.
--   - `privateState`: Private state with arbitrary (possibly entangled) normalized shield state, (3.3), PDF p.9, written using the diagonal twisting blocks.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, https://arxiv.org/abs/2609.32515v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder
open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]
variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]
variable [Fintype G2] [DecidableEq G2]

/-- Squared algebraic fidelity, (2.1), PDF p.5. The frozen primitive is ROOT fidelity. -/
def squaredFidelity (rho sigma : Matrix A A ℂ) : ℝ :=
  rootFidelity rho sigma ^ 2

/-- Normalized-state sine distance, (2.2), PDF p.5. -/
def sineDistance (rho sigma : Matrix A A ℂ) : ℝ :=
  Real.sqrt (1 - squaredFidelity rho sigma)

/-- Rectangular isometry; (2.6), PDF p.6. -/
def IsIsometry (U : Matrix B A ℂ) : Prop := Uᴴ * U = 1

/-- Fixed-dilation receiver map, on ALL operators, (2.6), PDF p.6. -/
def receiverChannel (U : Matrix (B × E) A ℂ) : Superop A B :=
  fun rho => traceRight (U * rho * Uᴴ)

/-- Complement of precisely the same dilation, (2.6), PDF p.6. -/
def complementaryChannel (U : Matrix (B × E) A ℂ) : Superop A E :=
  fun rho => traceLeft (U * rho * Uᴴ)

/-- Degrading direction, PDF p.6; Kraus normalization enforces CPTP. -/
def IsDegradable (U : Matrix (B × E) A ℂ) : Prop :=
  IsIsometry U ∧ ∃ D : Superop B E, IsChannel D ∧
    ∀ rho, complementaryChannel U rho = D (receiverChannel U rho)

/-- Antidegrading direction, PDF p.6. -/
def IsAntidegradable (U : Matrix (B × E) A ℂ) : Prop :=
  IsIsometry U ∧ ∃ D : Superop E B, IsChannel D ∧
    ∀ rho, receiverChannel U rho = D (complementaryChannel U rho)

/-- Maximum coherent information in bits, (2.7), PDF p.6. For an isometry on
nonempty finite systems the set is nonempty and bounded; its supremum is attained. -/
def maximumCoherentInformation (U : Matrix (B × E) A ℂ) : ℝ :=
  sSup {r | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
    r = vnEntropy (receiverChannel U rho) - vnEntropy (complementaryChannel U rho)}

/-- Tensor-power dilation, with all B and E factors grouped; (2.8), PDF p.6. -/
def dilationPower (U : Matrix (B × E) A ℂ) (n : ℕ) :
    Matrix ((Fin n → B) × (Fin n → E)) (Fin n → A) ℂ :=
  fun be a => ∏ i, U (be.1 i, be.2 i) (a i)

/-- Raw data of an unassisted collective code, Section 2.1, PDF p.6.
`Valid` below enforces normalization; no additional resources are fields. -/
structure PrivateCode (A B : Type*) (n : ℕ) where
  M : ℕ
  messages : Fin M → Matrix (Fin n → A) (Fin n → A) ℂ
  measurement : Fin M → Matrix (Fin n → B) (Fin n → B) ℂ

/-- Exactly the code assumptions of Section 2.1, PDF p.6. -/
def PrivateCode.Valid {n : ℕ} (code : PrivateCode A B n) : Prop :=
  0 < code.M ∧ (∀ m, IsDensityMatrix (code.messages m)) ∧ IsPOVM code.measurement

/-- Messagewise estimate/environment state (2.8), PDF p.6. The POVM is
applied to the B block of the ORIGINAL channel output. -/
def messageOutput (U : Matrix (B × E) A ℂ) {n : ℕ}
    (code : PrivateCode A B n) (m : Fin code.M) :
    Matrix (Fin code.M × (Fin n → E)) (Fin code.M × (Fin n → E)) ℂ :=
  let W := dilationPower U n
  let rho := W * code.messages m * Wᴴ
  fun je kf => if je.1 = kf.1 then
    ∑ b : Fin n → B, ∑ c : Fin n → B,
      code.measurement je.1 c b * rho (b, je.2) (c, kf.2)
    else 0

/-- Uniform classical message prior, (2.9), PDF p.6. -/
def jointOutput (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) :
    Matrix (Fin code.M × (Fin code.M × (Fin n → E)))
      (Fin code.M × (Fin code.M × (Fin n → E))) ℂ :=
  fun a b => if a.1 = b.1 then
    (code.M : ℂ)⁻¹ * messageOutput U code a.1 a.2 b.2 else 0

/-- Mixed ideal classical key tensor a common environment state, (2.10), PDF p.7. -/
def idealJoint (M : ℕ) (sigma : Matrix E E ℂ) :
    Matrix (Fin M × (Fin M × E)) (Fin M × (Fin M × E)) ℂ :=
  fun a b => if a.1 = a.2.1 ∧ b.1 = b.2.1 ∧ a.1 = b.1 then
    (M : ℂ)⁻¹ * sigma a.2.2 b.2.2 else 0

/-- Messagewise target; the same sigma is used for every m, (2.12), PDF p.7. -/
def idealMessage {M : ℕ} (m : Fin M) (sigma : Matrix E E ℂ) :
    Matrix (Fin M × E) (Fin M × E) ℂ :=
  fun a b => if a.1 = m ∧ b.1 = m then sigma a.2 b.2 else 0

/-- Optimized joint squared fidelity, (2.10), PDF p.7. On valid codes and
isometric dilations the optimization is nonempty, bounded in [0,1], and attained. -/
def optimizedFidelity (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) : ℝ :=
  sSup {r | ∃ sigma : Matrix (Fin n → E) (Fin n → E) ℂ,
    IsDensityMatrix sigma ∧ r = squaredFidelity (jointOutput U code) (idealJoint code.M sigma)}

/-- Actual environment marginal, (2.13), PDF p.7. -/
def environmentMarginal (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) :=
  traceLeft (traceLeft (jointOutput U code))

/-- Actual-marginal joint fidelity, (2.13), PDF p.7. -/
def marginalFidelity (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) : ℝ :=
  squaredFidelity (jointOutput U code) (idealJoint code.M (environmentMarginal U code))

/-- Uniform optimized infidelity, (2.11), PDF p.7. -/
def uniformError (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) : ℝ :=
  1 - optimizedFidelity U code

/-- Uniform actual-marginal infidelity, (2.13), PDF p.7. -/
def marginalError (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) : ℝ :=
  1 - marginalFidelity U code

/-- Min_sigma max_message optimized infidelity, (2.14), PDF p.7.
Validity ensures a nonempty message set and normalized-state optimization. -/
def maximalError (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) : ℝ :=
  sInf {r | ∃ sigma : Matrix (Fin n → E) (Fin n → E) ℂ, IsDensityMatrix sigma ∧
    r = sSup {s | ∃ m : Fin code.M,
      s = 1 - squaredFidelity (messageOutput U code m) (idealMessage m sigma)}}

/-- The three criteria of Section 2.1, PDF p.7. -/
inductive JointCriterion where
  | uniformOptimized
  | maximalOptimized
  | actualMarginal

/-- The named code error, PDF p.7. -/
def codeError (criterion : JointCriterion) (U : Matrix (B × E) A ℂ)
    {n : ℕ} (code : PrivateCode A B n) : ℝ :=
  match criterion with
  | .uniformOptimized => uniformError U code
  | .maximalOptimized => maximalError U code
  | .actualMarginal => marginalError U code

/-- Achievability (2.16), PDF p.7. Eventual lower bounds express the liminf
rate. The n=0 term is immaterial to both limits. -/
def AchievableRate (criterion : JointCriterion) (U : Matrix (B × E) A ℂ) (rate : ℝ) : Prop :=
  0 ≤ rate ∧ ∃ codes : (n : ℕ) → PrivateCode A B n,
    (∀ n, (codes n).Valid) ∧
    (∀ eta : ℝ, 0 < eta → ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0,
      rate - eta ≤ Real.logb 2 (codes n).M / (n : ℝ)) ∧
    Tendsto (fun n => codeError criterion U (codes n)) atTop (nhds 0)

/-- Capacity as the supremum of ACHIEVABLE nonnegative rates, not a named
coherent-information formula, PDF p.7. For finite nonempty physical systems
and an isometry this set contains zero and is bounded above by log_2 dim B. -/
def privateCapacity (criterion : JointCriterion) (U : Matrix (B × E) A ℂ) : ℝ :=
  sSup {r | AchievableRate criterion U r}

/-- Uniform witnesses for an optimized strong converse above threshold q.
Constants precede blocklength, messages, and every collective code (PDF pp.9,33). -/
def OptimizedDecay (U : Matrix (B × E) A ℂ) (q gap gamma : ℝ) (n0 : ℕ) : Prop :=
  ∀ n ≥ n0, ∀ code : PrivateCode A B n, code.Valid →
    (n : ℝ) * (q + gap) ≤ Real.logb 2 code.M →
    optimizedFidelity U code ≤ Real.rpow 2 (-gamma * n)

/-- Decoding error with the uniform prior, (D.10), PDF p.48. -/
def decodingError (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) : ℝ :=
  ∑ m : Fin code.M, ∑ j : Fin code.M,
    if m = j then 0 else ∑ e : Fin n → E, (jointOutput U code (m, j, e) (m, j, e)).re

/-- Trace-distance secrecy error with the actual marginal, (D.10), PDF p.48. -/
def secrecyError (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) : ℝ :=
  let omegaKE : Matrix (Fin code.M × (Fin n → E)) (Fin code.M × (Fin n → E)) ℂ :=
    fun a b => ∑ j : Fin code.M, jointOutput U code (a.1, j, a.2) (b.1, j, b.2)
  let target : Matrix (Fin code.M × (Fin n → E)) (Fin code.M × (Fin n → E)) ℂ :=
    fun a b => if a.1 = b.1 then (code.M : ℂ)⁻¹ * environmentMarginal U code a.2 b.2 else 0
  (1 / 2 : ℝ) * traceNorm (omegaKE - target)

/-- Literal orthogonal-flag erasure isometry, (7.10), PDF p.34.
The receiver and complement have `Option A` basis (none is the flag). -/
def erasureDilation (p : ℝ) : Matrix (Option A × Option A) A ℂ :=
  fun be a =>
    (if be.1 = some a ∧ be.2 = none then (Real.sqrt (1 - p) : ℂ) else 0) +
    (if be.1 = none ∧ be.2 = some a then (Real.sqrt p : ℂ) else 0)

/-- A privacy test from its diagonal twisting blocks, (3.3), PDF p.9.
Only the mm blocks contribute; arbitrary off-diagonal blocks extend them.
Tensor order is K,S,Khat,T. No separability is imposed on S,T. -/
def privacyTest {M : ℕ} (twist : Fin M → Matrix (S × T) (S × T) ℂ) :
    Matrix (Fin M × (S × (Fin M × T))) (Fin M × (S × (Fin M × T))) ℂ :=
  fun a b => if a.1 = a.2.2.1 ∧ b.1 = b.2.2.1 then
    (M : ℂ)⁻¹ * (twist a.1 * (twist b.1)ᴴ) (a.2.1, a.2.2.2) (b.2.1, b.2.2.2) else 0

/-- Decode then test on the full receiver input, retaining its auxiliary,
(3.18), PDF p.13. The map D changes only the receiver factor. -/
def decodedPrivacyTest {M : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (twist : Fin M → Matrix (S × T) (S × T) ℂ)
    (D : Matrix (Fin M × T) I ℂ) : Matrix (Fin M × (S × I)) (Fin M × (S × I)) ℂ :=
  fun a b => ∑ k : Fin M, ∑ l : Fin M, ∑ t : T, ∑ u : T,
    star (D (k, t) a.2.2) * privacyTest twist (a.1, a.2.1, k, t)
      (b.1, b.2.1, l, u) * D (l, u) b.2.2

/-- First projection on the common input KSXCYG1G2, (3.18), PDF p.13. -/
def firstTest {M : ℕ} {T1 : Type*} [Fintype T1] [DecidableEq T1]
    (twist : Fin M → Matrix (S × T1) (S × T1) ℂ)
    (D : Matrix (Fin M × T1) (X × (C × G1)) ℂ) :
    Matrix (Fin M × (S × (X × (C × (Y × (G1 × G2))))))
      (Fin M × (S × (X × (C × (Y × (G1 × G2)))))) ℂ :=
  fun a b => if a.2.2.2.2.1 = b.2.2.2.2.1 ∧ a.2.2.2.2.2.2 = b.2.2.2.2.2.2 then
    decodedPrivacyTest twist D (a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.2.1)
      (b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.2.1) else 0

/-- Second projection on the SAME space, identities on X,G1; (3.18), PDF p.13. -/
def secondTest {M : ℕ} {T2 : Type*} [Fintype T2] [DecidableEq T2]
    (twist : Fin M → Matrix (S × T2) (S × T2) ℂ)
    (D : Matrix (Fin M × T2) (C × (Y × G2)) ℂ) :
    Matrix (Fin M × (S × (X × (C × (Y × (G1 × G2))))))
      (Fin M × (S × (X × (C × (Y × (G1 × G2)))))) ℂ :=
  fun a b => if a.2.2.1 = b.2.2.1 ∧ a.2.2.2.2.2.1 = b.2.2.2.2.2.1 then
    decodedPrivacyTest twist D (a.1, a.2.1, a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2.2)
      (b.1, b.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2.2) else 0

/-- Number of agreeing coordinates, (4.2), PDF p.17 (not Hamming distance). -/
def agreementCount {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun j => x j = y j).card

/-- Uniform label matrix 2^(-n) 11^T, PDF p.19. -/
def uniformLabelMatrix (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  fun _ _ => ((2 : ℝ) ^ n)⁻¹

/-- Binomial SUM, not a single binomial coefficient; (4.12), PDF p.19. -/
def binomialVolume (n t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (t + 1), (n.choose j : ℝ)

/-- Subnormalized PSD states, Appendix B.1, PDF p.42. -/
def IsSubnormalized (rho : Matrix A A ℂ) : Prop :=
  rho.PosSemidef ∧ rho.trace.re ≤ 1

/-- Generalized fidelity for subnormalized states, (B.1), PDF p.42. -/
def generalizedFidelity (rho sigma : Matrix A A ℂ) : ℝ :=
  (rootFidelity rho sigma + Real.sqrt ((1 - rho.trace.re) * (1 - sigma.trace.re))) ^ 2

/-- Purified distance on subnormalized states, (B.1), PDF p.42. -/
def purifiedDistance (rho sigma : Matrix A A ℂ) : ℝ :=
  Real.sqrt (1 - generalizedFidelity rho sigma)

/-- Finite-real specialization of Hmax for NONZERO subnormalized rho,
(B.3), PDF p.42. The log is outside the supremum of algebraic fidelities,
which is positive for nonzero rho on positive-dimensional systems.
At rho=0 this helper is unused (Hmax there is -infinity). -/
def conditionalMaxEntropyValue (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  Real.logb 2 (sSup {f | ∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
    f = squaredFidelity rho (Matrix.kronecker (1 : Matrix A A ℂ) sigma)})

/-- Real smooth Hmax at NORMALIZED center, 0≤epsilon<1, (B.4), PDF p.43.
The ball contains subnormalized states. Zero is excluded explicitly because
its distance from a normalized center is 1; it cannot be a feasible point.
On this domain the nonempty entropy set is bounded above and below. -/
def smoothConditionalMaxEntropy (rho : Matrix (A × B) (A × B) ℂ) (epsilon : ℝ) : ℝ :=
  sInf {h | ∃ tau : Matrix (A × B) (A × B) ℂ,
    IsSubnormalized tau ∧ tau ≠ 0 ∧ purifiedDistance tau rho ≤ epsilon ∧
      h = conditionalMaxEntropyValue tau}

/-- Conditional von Neumann entropy, (2.5), PDF p.6. -/
def conditionalEntropy (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy rho - vnEntropy (traceLeft rho)

/-- Grouped tensor power of a bipartite matrix, PDF pp.30–31,43–45. -/
def groupedPower (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  fun a b => ∏ i, rho (a.1 i, a.2 i) (b.1 i, b.2 i)

/-- Postselection scalar, (6.11)/(B.12), PDF pp.30,44. -/
def postselectionFactor (a n : ℕ) : ℝ := (n + 1 : ℝ) ^ (a ^ 2)

/-- Dimension-only AEP constant, (6.11), PDF p.30. -/
def entropyDimensionConstant (d : ℕ) : ℝ := 8 * Real.logb 2 (2 * d + 1)

/-- Recovery-error correction, (6.11)–(6.12), PDF p.30, defined explicitly
for positive delta. No entropy theorem is a hidden input to this definition. -/
def filterDimensionCorrection (a d n : ℕ) (delta : ℝ) : ℝ :=
  let g := postselectionFactor a n
  let u := delta ^ 2 / 16
  let v := u ^ 2 / (32 * g)
  entropyDimensionConstant d * Real.sqrt ((n : ℝ) * Real.logb 2 (2 / v ^ 2)) +
    3 * Real.logb 2 g + 8 * Real.logb 2 (1 / delta) + 19

/-- Group the output of T tensor n into F^n,E'^n, Appendix B.2, PDF p.43. -/
def groupedChannelPower (Tmap : Superop A (B × E)) (n : ℕ) :
    Superop (Fin n → A) ((Fin n → B) × (Fin n → E)) :=
  fun rho =>
    let out := piSuperop (fun _ : Fin n => Tmap) rho
    fun a b => out (fun i => (a.1 i, a.2 i)) (fun i => (b.1 i, b.2 i))

/-- Apply a channel to the FIRST factor, retaining the exact reference,
used in (5.2), PDF p.24. Off-diagonal reference blocks are retained. -/
def mapFirst (Phi : Superop A B) : Superop (A × R) (B × R) :=
  fun rho a b => Phi (fun i j => rho (i, a.2) (j, b.2)) a.1 b.1

/-- The unnormalized linear-filter ket on the original state, (5.1), PDF p.24. -/
def filteredKet (Z : Matrix C A ℂ) (psi : EuclideanSpace ℂ ((A × B) × R)) :
    EuclideanSpace ℂ ((C × B) × R) :=
  WithLp.toLp 2 (fun cbr => ∑ a : A, Z cbr.1.1 a * psi ((a, cbr.1.2), cbr.2))

/-- Single-filter recovery guarantee, (5.1)–(5.3), PDF p.24.
No probability lower bound is imposed on the one selected filter. -/
def FilterGuarantee (psi : EuclideanSpace ℂ ((A × B) × R)) (delta : ℝ)
    (L : ℕ) (Z : Matrix (Fin L) A ℂ) (rec : Superop (Fin L × B) (A × B)) : Prop :=
  let raw := filteredKet Z psi
  let nu := ‖raw‖ ^ 2
  let chi := (Real.sqrt nu)⁻¹ • raw
  0 < nu ∧ IsState chi ∧ IsChannel rec ∧
  sineDistance (mapFirst rec (pureDensity chi)) (pureDensity psi) ≤ delta ∧
  Real.logb 2 L ≤ max
    (smoothConditionalMaxEntropy (traceRight (pureDensity psi)) (delta ^ 2 / 16) +
      4 * Real.logb 2 (1 / delta) + 4) 0 + 1

section SanityChecks

/-! Sanity checks for the new definitions (proofs only for definitions, not paper results). -/

example (U : Matrix (B × E) A ℂ) (be : (Fin 0 → B) × (Fin 0 → E)) (a : Fin 0 → A) :
    dilationPower U 0 be a = 1 := by simp [dilationPower]

example : uniformLabelMatrix 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) = 1 := by
  simp [uniformLabelMatrix]

example {n : ℕ} (x : Fin n → Bool) : agreementCount x x = n := by
  simp [agreementCount]

example (n : ℕ) : binomialVolume n 0 = 1 := by
  simp [binomialVolume]

example (M : ℕ) : idealJoint M (0 : Matrix E E ℂ) = 0 := by
  ext a b
  simp [idealJoint]

example (U : Matrix (B × E) A ℂ) : receiverChannel U 0 = 0 := by
  ext a b
  simp [receiverChannel, traceRight]

example (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) :
    uniformError U code = 1 - optimizedFidelity U code := rfl

example (a : ℕ) : postselectionFactor a 0 = 1 := by simp [postselectionFactor]

example {n : ℕ} (code : PrivateCode A B n) (h : code.Valid) : 0 < code.M := h.1

end SanityChecks

/-- Independent real standard Gaussians for real/imaginary matrix entries,
(5.5), PDF p.25. The law is a finite product probability measure. -/
def gaussianFilterLaw (L : ℕ) (A : Type*) [Fintype A] :
    Measure ((Fin L × (A × Bool)) → ℝ) :=
  Measure.pi (fun _ => ProbabilityTheory.gaussianReal 0 1)

/-- Complex Gaussian matrix with E|Z_ai|^2=1/L, (5.5), PDF p.25. -/
def gaussianFilter (L : ℕ) (z : (Fin L × (A × Bool)) → ℝ) : Matrix (Fin L) A ℂ :=
  fun a i => ((z (a, i, false) : ℂ) + Complex.I * (z (a, i, true) : ℂ)) /
    (Real.sqrt (2 * (L : ℝ)) : ℂ)

/-- CP (not necessarily TP) reference map Gamma_Z, (5.6), PDF p.25. -/
def referenceFilterMap (Z : Matrix C A ℂ) (tau : Matrix (A × R) (A × R) ℂ) : Matrix R R ℂ :=
  let W := Matrix.kronecker Z (1 : Matrix R R ℂ)
  traceLeft (W * tau * Wᴴ)

/-- Flagged identity dilation (D.9), PDF p.48: false is flag zero. -/
def flaggedIdentityDilation (M : ℕ) (p : ℝ) : Matrix ((Fin M × Bool) × Bool) (Fin M) ℂ :=
  fun be m => if be.1.1 = m ∧ be.1.2 = be.2 then
    (if be.2 then (Real.sqrt (1 - p) : ℂ) else (Real.sqrt p : ℂ)) else 0

/-- The explicit one-use code in Appendix D.2, PDF p.48. On flag one the
reported message is the cyclic successor, irrespective of correctness. -/
def flaggedIdentityCode (M : ℕ) : PrivateCode (Fin M) (Fin M × Bool) 1 where
  M := M
  messages := fun m a b => if a 0 = m ∧ b 0 = m then 1 else 0
  measurement := fun j a b => if a = b ∧
    (if (a 0).2 then ((a 0).1.val + 1) % M else (a 0).1.val) = j.val then 1 else 0

/-- The classical output (D.6), constructed from the flags, PDF p.48. -/
def flaggedExampleOutput (M : ℕ) (p : ℝ) :
    Matrix (Fin M × (Fin M × (Fin 1 → Bool))) (Fin M × (Fin M × (Fin 1 → Bool))) ℂ :=
  fun a b => if a = b then (M : ℂ)⁻¹ *
    ((if a.1 = a.2.1 ∧ a.2.2 0 = false then (p : ℂ) else 0) +
      (if a.2.1.val = (a.1.val + 1) % M ∧ a.2.2 0 = true then ((1 - p : ℝ) : ℂ) else 0))
    else 0

/-- Canonical coherent ket (3.5)–(3.7), PDF pp.10–11. S=Kcopy×S1 and
T=(Khatcopy×B^n)×Taux. Taux is local and starts in the basis ket `none`.
All tensor permutations are explicit in the coordinate formula. -/
def coherentCodeKet (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n)
    (r t : ℕ) (pur : Fin code.M → EuclideanSpace ℂ (Fin r × (Fin n → A))) :
    EuclideanSpace ℂ ((Fin code.M × ((Fin code.M × Fin r) ×
      (Fin code.M × ((Fin code.M × (Fin n → B)) × Option (Fin t))))) × (Fin n → E)) :=
  WithLp.toLp 2 (fun z =>
    if z.1.2.1.1 = z.1.1 ∧ z.1.2.2.2.1.1 = z.1.2.2.1 ∧ z.1.2.2.2.2 = none then
      ((Real.sqrt code.M)⁻¹ : ℂ) *
      ∑ b : Fin n → B, ∑ a : Fin n → A,
        (cfc Real.sqrt (code.measurement z.1.2.2.1)) z.1.2.2.2.1.2 b *
          dilationPower U n (b, z.2) a * pur z.1.1 (z.1.2.1.2, a)
    else 0)

/-- Trace both shields out of a coherent ket, (3.8), PDF p.11. -/
def coherentClassicalMarginal {M : ℕ}
    (psi : EuclideanSpace ℂ ((Fin M × (S × (Fin M × T))) × E)) :
    Matrix (Fin M × (Fin M × E)) (Fin M × (Fin M × E)) ℂ :=
  fun a b => ∑ s : S, ∑ t : T,
    psi ((a.1, s, a.2.1, t), a.2.2) * star (psi ((b.1, s, b.2.1, t), b.2.2))

/-- Exchange just coordinate j in two receiver copies, Section 4.1, PDF p.17. -/
def swapReceiverCoordinate {M n : ℕ} (j : Fin n)
    (z : Fin M × (S × (C × ((Fin n → B) × (Fin n → B))))) :=
  (z.1, z.2.1, z.2.2.1,
    Function.update z.2.2.2.1 j (z.2.2.2.2 j),
    Function.update z.2.2.2.2 j (z.2.2.2.1 j))

/-- Receiver marginal with one initialized local auxiliary, PDF pp.17–18.
The other receiver copy is traced out; the sender shield is retained. -/
def symmetricReceiverMarginal {M n : ℕ}
    (theta : Matrix (Fin M × (S × (C × ((Fin n → B) × (Fin n → B)))))
      (Fin M × (S × (C × ((Fin n → B) × (Fin n → B))))) ℂ) (g : G1) :
    Matrix (Fin M × (S × (C × ((Fin n → B) × G1))))
      (Fin M × (S × (C × ((Fin n → B) × G1)))) ℂ :=
  fun a b => if a.2.2.2.2 = g ∧ b.2.2.2.2 = g then
    ∑ e : Fin n → B,
      theta (a.1, a.2.1, a.2.2.1, a.2.2.2.1, e)
        (b.1, b.2.1, b.2.2.1, b.2.2.2.1, e) else 0

/-- Composed dilation, with tensor order F,(E',E), (6.1)–(6.2), PDF p.28. -/
def symmetricDilation (U : Matrix (B × E) A ℂ) (V : Matrix (R × E) B ℂ) :
    Matrix (R × (E × E)) A ℂ :=
  fun fee a => ∑ b : B, V (fee.1, fee.2.1) b * U (b, fee.2.2) a

/-- Basis-independent range form of the fixed symmetric factorization,
(6.1)–(6.2), PDF p.28. The last equality is symmetry of the ISOMETRY,
not merely equality of its two marginal channels. -/
def IsSymmetricFactorization (U : Matrix (B × E) A ℂ) (V : Matrix (R × E) B ℂ) : Prop :=
  IsIsometry U ∧ IsIsometry V ∧
    (∀ rho, traceLeft (V * receiverChannel U rho * Vᴴ) = complementaryChannel U rho) ∧
    (∀ f e1 e2 a, symmetricDilation U V (f, e1, e2) a = symmetricDilation U V (f, e2, e1) a)

/-- Swap on the two identical environment factors, Appendix A, PDF pp.39–42. -/
def environmentSwap : Matrix (E × E) (E × E) ℂ :=
  fun a b => if a = (b.2, b.1) then 1 else 0

/-- Independent receiver mixed qubit with its specified purification,
Appendix A.2, PDF pp.41–42. -/
def mixedQubitExtension (U : Matrix (B × E) A ℂ) :
    Matrix ((B × Bool) × (E × Bool)) A ℂ :=
  fun be a => if be.1.2 = be.2.2 then ((Real.sqrt 2)⁻¹ : ℂ) * U (be.1.1, be.2.1) a else 0

/-- The corresponding original code, ignoring the appended receiver qubits,
(A.13), PDF p.42. No input message state is changed. -/
def extendCode {n : ℕ} (code : PrivateCode A B n) : PrivateCode A (B × Bool) n where
  M := code.M
  messages := code.messages
  measurement := fun j a b => if (fun i => (a i).2) = (fun i => (b i).2) then
    code.measurement j (fun i => (a i).1) (fun i => (b i).1) else 0

/-- Coherent encoder output reordered as (F^n E'^n)(Rref E^n), (6.6),
PDF p.29. Rref includes the sender key and shield in the code application. -/
def symmetricEncoderOutput {F : Type*} [Fintype F] [DecidableEq F]
    (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ) (n : ℕ)
    (phi : EuclideanSpace ℂ (R × (Fin n → A))) :
    EuclideanSpace ℂ (((Fin n → F) × (Fin n → E)) × (R × (Fin n → E))) :=
  WithLp.toLp 2 (fun z => ∑ a : Fin n → A,
    (∏ i, symmetricDilation U V (z.1.1 i, z.1.2 i, z.2.2 i) (a i)) * phi (z.2.1, a))

example (L : ℕ) (z : (Fin L × (A × Bool)) → ℝ) (a : Fin L) (i : A)
    (hz : z (a, i, false) = 0) (hi : z (a, i, true) = 0) :
    gaussianFilter L z a i = 0 := by simp [gaussianFilter, hz, hi]

example (Z : Matrix C A ℂ) : referenceFilterMap (R := R) Z 0 = 0 := by
  ext r s
  simp [referenceFilterMap, traceLeft]

example (U : Matrix (B × E) A ℂ) (b : B) (e : E) (a : A) :
    mixedQubitExtension U ((b, false), (e, true)) a = 0 := by simp [mixedQubitExtension]

example {n : ℕ} (code : PrivateCode A B n) : (extendCode code).messages = code.messages := rfl

example (M : ℕ) : (flaggedIdentityCode M).M = M := rfl

example : IsSubnormalized (0 : Matrix A A ℂ) := by
  exact ⟨Matrix.PosSemidef.zero, by simp⟩

/-- Extended conditional min-entropy (B.2), PDF p.42. The real exponent
set is embedded BEFORE taking the EReal supremum, preserving +infinity at zero. -/
def conditionalMinEntropy (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sSup {h : EReal | ∃ lambda : ℝ, h = (lambda : EReal) ∧
    ∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
      ((Real.rpow 2 (-lambda) : ℂ) • Matrix.kronecker (1 : Matrix A A ℂ) sigma - rho).PosSemidef}

/-- Extended conditional max-entropy (B.3), PDF p.42. The zero operator
has value -infinity, rather than Real.logb's default value at zero. -/
def conditionalMaxEntropy (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  if rho = 0 then ⊥ else (conditionalMaxEntropyValue rho : EReal)

/-- Extended smooth min-entropy on the full subnormalized ball, (B.4), PDF p.43. -/
def smoothConditionalMinEntropy (rho : Matrix (A × B) (A × B) ℂ) (epsilon : ℝ) : EReal :=
  sSup {h | ∃ tau : Matrix (A × B) (A × B) ℂ,
    IsSubnormalized tau ∧ purifiedDistance tau rho ≤ epsilon ∧ h = conditionalMinEntropy tau}

/-- Extended smooth max-entropy on the full subnormalized ball, (B.4), PDF p.43.
The real specialization above is used only at normalized centers and epsilon<1. -/
def smoothConditionalMaxEntropyExtended (rho : Matrix (A × B) (A × B) ℂ) (epsilon : ℝ) : EReal :=
  sInf {h | ∃ tau : Matrix (A × B) (A × B) ℂ,
    IsSubnormalized tau ∧ purifiedDistance tau rho ≤ epsilon ∧ h = conditionalMaxEntropy tau}

/-- Entangled KEY KET (3.1), PDF p.9, distinct from the mixed ideal
classical key used in the error criterion. Meaningful for M≥1. -/
def maximallyEntangledKey (M : ℕ) : EuclideanSpace ℂ (Fin M × Fin M) :=
  WithLp.toLp 2 (fun a => if a.1 = a.2 then ((Real.sqrt M)⁻¹ : ℂ) else 0)

/-- Mixed uniform perfectly correlated classical key, (2.10), PDF p.7. -/
def idealClassicalKey (M : ℕ) : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ :=
  fun a b => if a.1 = a.2 ∧ b.1 = b.2 ∧ a.1 = b.1 then (M : ℂ)⁻¹ else 0

/-- Full controlled twisting unitary, (3.2), PDF p.9. Each block must be
unitary in uses of this definition; off-diagonal key blocks are unrestricted. -/
def twistingUnitary {M : ℕ}
    (blocks : Fin M → Fin M → Matrix (S × T) (S × T) ℂ) :
    Matrix (Fin M × (S × (Fin M × T))) (Fin M × (S × (Fin M × T))) ℂ :=
  fun a b => if a.1 = b.1 ∧ a.2.2.1 = b.2.2.1 then
    blocks a.1 a.2.2.1 (a.2.1, a.2.2.2) (b.2.1, b.2.2.2) else 0

/-- Private state with arbitrary (possibly entangled) normalized shield
state, (3.3), PDF p.9, written using the diagonal twisting blocks. -/
def privateState {M : ℕ} (twist : Fin M → Matrix (S × T) (S × T) ℂ)
    (tau : Matrix (S × T) (S × T) ℂ) :
    Matrix (Fin M × (S × (Fin M × T))) (Fin M × (S × (Fin M × T))) ℂ :=
  fun a b => if a.1 = a.2.2.1 ∧ b.1 = b.2.2.1 then
    (M : ℂ)⁻¹ * (twist a.1 * tau * (twist b.1)ᴴ)
      (a.2.1, a.2.2.2) (b.2.1, b.2.2.2) else 0

example : squaredFidelity (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 1 := by
  simp [squaredFidelity, rootFidelity, cfc_one]

example : sineDistance (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 := by
  simp [sineDistance, squaredFidelity, rootFidelity, cfc_one]

example : purifiedDistance (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 1 := by
  simp [purifiedDistance, generalizedFidelity, rootFidelity, cfc_zero]

example : conditionalMaxEntropy (0 : Matrix (A × B) (A × B) ℂ) = ⊥ := by
  simp [conditionalMaxEntropy]

example (psi : EuclideanSpace ℂ ((A × B) × R)) :
    filteredKet (0 : Matrix C A ℂ) psi = 0 := by
  ext cbr
  simp [filteredKet]

example {M : ℕ} (twist : Fin M → Matrix (S × T) (S × T) ℂ) :
    privateState twist 1 = privacyTest twist := by
  ext a b
  simp [privateState, privacyTest]

end QAlgorithms.Papers.Independent.Information100.P67


