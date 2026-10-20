-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12
-- name    : QAlgorithms_Papers_Independent_Frontier30_P12
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T17:03:19.890687+00:00
-- url     : https://prove2.me/theorems/4d28c7f2-f4b5-4554-a194-e354ef51ab6c
-- title:
--   Definitions for Distillation of secret key and entanglement from quantum states
-- statement:
--   The objects the formalized statements of *Distillation of secret key and entanglement from quantum states* (arXiv:quant-ph/0306078) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsStochastic`: PDF p.5: a finite stochastic channel; the first argument is the input.
--   - `lawCopies`: PDF p.2: the n independent classical copies.
--   - `channelWordState`: PDF p.2: memoryless cq output, via the accepted tensor-word map. Only CQData.state is read by that map; its unused probability slot is zero. This adapter does not assert that the auxiliary CQData record is normalized.
--   - `bipCopies`: PDF pp.2,6: independent bipartite copies, regrouped by party.
--   - `cqqCopies`: PDF p.2: independent cqq conditional BE states for each classical word, regrouped into Bob's and Eve's n-copy registers.
--   - `triCopies`: PDF pp.2,5: independent tripartite copies, regrouped by party.
--   - `IsCqq`: PDF p.2, eq.(1): normalized cqq data; no purification of BE is required.
--   - `cqqAdvantage`: PDF p.2: I(X;B)-I(X;E) of a cqq source.
--   - `typeClass`: PDF p.11, Appendix A: the exact type class. Positive n is required at use sites.
--   - `IsTypeLength`: PDF pp.4,11: compatible lengths for a fixed empirical distribution. Distinct from accepted P26.Compatible, a predicate on algebras and channels.
--   - `typeSampleProb`: PDF p.4: the uniform independent-with-replacement codebook law, written as finite counting probability. Repeated words are permitted.
--   - `typeMean`: PDF p.4: the uniform mean output sigma(P).
--   - `typeOutputAverage`: PDF p.4: empirical channel-output matrix average for a sampled codebook. Distinct from ProbabilisticCancellation.sampleMean, a scalar signed-shot estimator.
--   - `GoodCode`: PDF p.4, Proposition 5: average, rather than maximum, decoding error.
--   - `normalized`: PDF pp.2,5,9: a zero-weight conditional state has a fixed normalized version. The fallback is maximally mixed; all uses have a nonempty underlying register.
--   - `SecretBlocks`: PDF p.2: normalized conditional versions and one common state on transcript+E. The norm is the full Schatten 1 norm. For zero key mass the conditional version is arbitrary, but must still be normalized and close to the same common state.
--   - `KeyGood`: PDF p.2: all three key criteria, with the full l1 distance from uniform.
--   - `CqqProtocol`: PDF p.2: finite cqq one-way protocol on n copies. Alice uses a stochastic map X^n -> (public transcript,key); Bob's POVM depends only on that transcript.
--   - `CqqProtocol.Valid`: PDF p.2: precisely the legal cqq encoding and decoding operations.
--   - `CqqProtocol.joint`: PDF p.2: the actual joint key law after the protocol.
--   - `CqqProtocol.blocks`: PDF p.2: Eve receives a classical copy of the public transcript. These are unnormalized blocks indexed by Alice's key, after forgetting Bob's outcome.
--   - `CqqAchieves`: PDF p.2: an evaluated sequence with errors tending to zero and ONE finite public-rate bound F for every block length. The sequence exists for every n, including a harmless zero-copy member.
--   - `cqqKeyCapacity`: PDF p.2: operational forward secret-key capacity; no entropic substitute.
--   - `QuantumKeyProtocol`: PDF pp.5--6: finite general-state one-way key protocol. Alice measures Q_(transcript,key) and Bob measures conditional on the authenticated transcript.
--   - `QuantumKeyProtocol.Valid`: PDF p.6: all finite POVMs on Alice are allowed, without a purity assumption.
--   - `measuredBlock`: PDF p.5: the UNNORMALIZED conditional BE block of a POVM outcome. This is Tr_A(rho (Q tensor I)); there is no additional factor P(x).
--   - `QuantumKeyProtocol.joint`: PDF p.6: the physically evaluated joint law of Alice and Bob's keys.
--   - `QuantumKeyProtocol.blocks`: PDF pp.5--6: Eve's evaluated public-transcript blocks, diagonal in transcript.
--   - `QuantumKeyAchieves`: PDF p.6: operational general-state secret-key sequences, using all three p.2 criteria and one fixed finite F before n.
--   - `quantumKeyCapacity`: PDF pp.5--6: the general-state forward key capacity, defined operationally.
--   - `processedBlocks`: PDF p.5: the unnormalized (u,t) BE blocks of X -> U -> T.
--   - `conditionalAdvantage`: PDF p.5: I(U;B|T)-I(U;E|T), evaluated from unnormalized joint blocks. Every zero-mass branch is weighted by zero after choosing a normalized version.
--   - `cqqValues`: PDF p.5: the UNRESTRICTED classical preprocessing objective values.
--   - `cqqSingle`: PDF p.5: single-copy key optimization, independently of operational rates. Theorem 6 asserts that this supremum is a maximum with the printed range bounds.
--   - `quantumProcessed`: PDF p.5: measured-state (x,t) blocks. Printed redundant P(x) is omitted.
--   - `quantumKeyValues`: PDF p.5: unrestricted finite POVM and classical T|X objective values.
--   - `quantumKeySingle`: PDF p.5: general-state single-copy key objective.
--   - `RectangularKrausData`: PDF p.6: finite quantum instrument with arbitrary output dimension and unobserved Kraus index; the classical branch is l. This is raw rectangular data on arbitrary register types, with validity checked separately. Accepted P08.Instrument uses Fin dimensions and bundles completeness; Nonconvex.Instrument has square continuous-linear maps with norm completeness. Neither is this data interface.
--   - `RectangularKrausData.Valid`: PDF p.6: the CP branches sum to a trace-preserving map.
--   - `RectangularKrausData.branch`: PDF p.9: a branch applied to the ACTUAL input, identity on Bob.
--   - `BobChannel`: PDF p.6: Bob's arbitrary finite-dimensional CPTP map in Kraus form.
--   - `BobChannel.Valid`: PDF p.6: completeness of Bob's local Kraus family.
--   - `EntProtocol`: PDF p.6: a one-way EPR protocol. Alice outputs on the M-dimensional target support; the only shared input is the supplied n-copy state.
--   - `EntProtocol.Valid`: PDF p.6: legality of the instrument and every transcript-dependent Bob map.
--   - `EntProtocol.output`: PDF p.6: branch-averaged output sum_l (T_l tensor R_l)(rho^n).
--   - `eprFidelity`: PDF pp.6,12: squared fidelity with the pure EPR target.
--   - `EntAchieves`: PDF p.6: a fixed protocol sequence attaining a rate; no good coherent protocol is assumed as a theorem hypothesis. Classical cost is log l.
--   - `entCapacity`: PDF p.6: the one-way EPR capacity, defined through evaluated protocols.
--   - `coherentInfo`: PDF p.7: coherent information I_c(A>B).
--   - `instrumentYield`: PDF p.9: the weighted normalized-branch objective of a genuine instrument.
--   - `entValues`: PDF p.9: unrestricted objective values, allowing arbitrary finite Alice output.
--   - `entSingle`: PDF p.9: single-copy instrument optimization. Attainment is a theorem.
--   - `squareInstrument`: PDF p.9: the square, single-Kraus instrument used by the restricted optimizer.
--   - `marginalAE`: PDF p.8: the AE marginal of a tripartite state, tracing only Bob.
--   - `mutualAE`: PDF p.8: mutual information I(A:E) of a fixed purification.
--   - `pauliBellVector`: PDF pp.8--9: Bell convention Phi_00=Phi+, Phi_01=Phi-, Phi_10=Psi+, Phi_11=Psi-. Bits are Bool, false=0, true=1. Obtained by bit/phase flips of the accepted maximally entangled vector, rather than re-declaring it.
--   - `bellPurification`: PDF p.8: manifestly normalized Bell-sum purification. This avoids the printed 1/sqrt(1) typo in the subsequent Schmidt expression.
--   - `bellConditional`: PDF p.9: normalized BE states conditional on Alice's computational outcome. The outcome probabilities are exactly 1/2, including rank-deficient mixtures.
--   - `bellBitLaw`: PDF p.9: the bit-flip distribution p_00+p_01, p_10+p_11.
--   - `finBipCopies`: PDF p.10: regroup n copies into the finite-dimensional interface of the accepted finite-LOCC semantics, using the canonical finite-function equivalence.
--   - `twoWayValues`: PDF p.10: actual two-way LOCC output coherent-information values. Arbitrary finite positive output dimensions and unbounded finite round counts are allowed; the supremum includes approximation by finite protocols, without attainment.
--   - `twoWaySingle`: PDF p.10: optimized coherent information after evaluated two-way LOCC.
--   - `TwoWayAchievable`: PDF pp.9--10: two-way EPR rate using genuine finite LOCC, evaluated on the independent-copy input. Local environments may be discarded, no shared ancilla is supplied, and approximation is expressed by EPR fidelity tending to one.
--   - `twoWayCapacity`: PDF p.10: operational two-way EPR distillable entanglement.
--   - `CqqRestrictedMaximum`: PDF p.5, Theorem 6: a maximum of the unrestricted objective, attained with |T|<=|X|, |U|<=|X|^2 and deterministic T=f(U).
--   - `QuantumRestrictedMaximum`: PDF pp.5,15, Theorem 8: attainment of the unrestricted POVM objective with |T|<=d_A^2, |X|<=d_A^4 and deterministic T=f(X).
--   - `EntRestrictedMaximum`: PDF p.9: unrestricted instrument optimization is attained by a square positive single-Kraus instrument on the original Alice space, with L<=d_A^2.
--   - `quantumMutualInfo`: PDF p.2: quantum mutual information for a bipartite state.
--   - `bellDiagonalState`: PDF pp.6,8: four-Bell-state mixture with the paper's Bell numbering. Distinct from accepted Dependency50.P36.bellMixture, a one-parameter mixture of only two Bell states on Fin 2 registers.
--   - `EntSplitAttains`: PDF pp.8--9: an attained entanglement rate together with two public message components on the SAME protocol sequence. The instrument's l outcomes identify Fin(code_n) x Fin(phase_n), so the component cardinalities describe real messages.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, https://arxiv.org/abs/quant-ph/0306078v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

/-!
Statements from Devetak--Winter, arXiv:quant-ph/0306078v1 (2003).
All new definitions are local to this paper; shared concepts reuse the pinned
library. Rates are operational; no entropy formula is used to define a capacity. Theorem 8 corrects the missing 1/n and
redundant P(x) in the printed statement, as fixed by its preceding measured-state
formula and the converse on PDF p.6. Independent moderation remains required.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- PDF p.5: a finite stochastic channel; the first argument is the input. -/
def IsStochastic {X Y : Type} [Fintype Y] (q : X → Y → ℝ) : Prop :=
  ∀ x, IsLaw (q x)

/-- PDF p.2: the n independent classical copies. -/
def lawCopies {X : Type} (p : X → ℝ) (n : ℕ) (x : Fin n → X) : ℝ :=
  ∏ i, p (x i)

/-- PDF p.2: memoryless cq output, via the accepted tensor-word map.
Only CQData.state is read by that map; its unused probability slot is zero.
This adapter does not assert that the auxiliary CQData record is normalized. -/
def channelWordState {X H : Type} (W : X → Op H) {n : ℕ} (x : Fin n → X) :
    Op (Fin n → H) :=
  QAlgorithms.Papers.Independent.Dependency50.P07.wordState
    ⟨fun _ => 0, W⟩ n x

/-- PDF pp.2,6: independent bipartite copies, regrouped by party. -/
def bipCopies {A B : Type} (rho : Op (A × B)) (n : ℕ) :
    Op ((Fin n → A) × (Fin n → B)) :=
  fun y z => ∏ i, rho (y.1 i,y.2 i) (z.1 i,z.2 i)

/-- PDF p.2: independent cqq conditional BE states for each classical word,
regrouped into Bob's and Eve's n-copy registers. -/
def cqqCopies {X B E : Type} (W : X → Op (B × E)) {n : ℕ}
    (x : Fin n → X) : Op ((Fin n → B) × (Fin n → E)) :=
  fun y z => ∏ i, W (x i) (y.1 i,y.2 i) (z.1 i,z.2 i)

/-- PDF pp.2,5: independent tripartite copies, regrouped by party. -/
def triCopies {A B E : Type} (rho : Op (A × (B × E))) (n : ℕ) :
    Op ((Fin n → A) × ((Fin n → B) × (Fin n → E))) :=
  fun y z => ∏ i, rho (y.1 i,(y.2.1 i,y.2.2 i)) (z.1 i,(z.2.1 i,z.2.2 i))

/-- PDF p.2, eq.(1): normalized cqq data; no purification of BE is required. -/
def IsCqq {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    (p : X → ℝ) (W : X → Op (B × E)) : Prop :=
  IsLaw p ∧ ∀ x, QAlgorithms.IsDensityMatrix (W x)

/-- PDF p.2: I(X;B)-I(X;E) of a cqq source. -/
def cqqAdvantage {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    (p : X → ℝ) (W : X → Op (B × E)) : ℝ :=
  labelInformation p (fun x => QAlgorithms.traceRight (W x)) -
    labelInformation p (fun x => QAlgorithms.traceLeft (W x))

/-- PDF p.11, Appendix A: the exact type class. Positive n is required at use sites. -/
def typeClass {X : Type} [Fintype X] (p : X → ℝ) (n : ℕ) :
    Finset (Fin n → X) :=
  Finset.univ.filter fun x => ∀ a,
    ((Finset.univ.filter fun i => x i = a).card : ℝ) / n = p a

/-- PDF pp.4,11: compatible lengths for a fixed empirical distribution.
Distinct from accepted P26.Compatible, a predicate on algebras and channels. -/
def IsTypeLength {X : Type} [Fintype X] (p : X → ℝ) (n : ℕ) : Prop :=
  0 < n ∧ (typeClass p n).Nonempty

/-- PDF p.4: the uniform independent-with-replacement codebook law, written as
finite counting probability. Repeated words are permitted. -/
def typeSampleProb {X : Type} [Fintype X] (p : X → ℝ) (n m : ℕ)
    (event : (Fin m → (Fin n → X)) → Prop) : ℝ :=
  let sample : Finset (Fin m → (Fin n → X)) :=
    Finset.univ.filter fun C => ∀ j, C j ∈ typeClass p n
  ((sample.filter event).card : ℝ) / sample.card

/-- PDF p.4: the uniform mean output sigma(P). -/
def typeMean {X H : Type} [Fintype X] (p : X → ℝ)
    (W : X → Op H) (n : ℕ) : Op (Fin n → H) :=
  (((typeClass p n).card : ℂ)⁻¹) • ∑ x ∈ typeClass p n, channelWordState W x

/-- PDF p.4: empirical channel-output matrix average for a sampled codebook.
Distinct from ProbabilisticCancellation.sampleMean, a scalar signed-shot estimator. -/
def typeOutputAverage {X H : Type} (W : X → Op H) {n m : ℕ}
    (C : Fin m → (Fin n → X)) : Op (Fin n → H) :=
  ((m : ℂ)⁻¹) • ∑ j, channelWordState W (C j)

/-- PDF p.4, Proposition 5: average, rather than maximum, decoding error. -/
def GoodCode {X H : Type} [Fintype H] (W : X → Op H) {n m : ℕ}
    (C : Fin m → (Fin n → X)) (eps : ℝ) : Prop :=
  ∃ D : Fin m → Op (Fin n → H), QAlgorithms.IsPOVM D ∧
    1 - eps ≤ (m : ℝ)⁻¹ * ∑ j, QAlgorithms.effectProb (D j) (channelWordState W (C j))

/-- PDF pp.2,5,9: a zero-weight conditional state has a fixed normalized version.
The fallback is maximally mixed; all uses have a nonempty underlying register. -/
def normalized {H : Type} [Fintype H] (s : Op H) : Op H :=
  if s.trace.re = 0 then ((Fintype.card H : ℂ)⁻¹) • 1
  else ((s.trace.re)⁻¹ : ℂ) • s

/-- PDF p.2: normalized conditional versions and one common state on transcript+E.
The norm is the full Schatten 1 norm. For zero key mass the conditional version
is arbitrary, but must still be normalized and close to the same common state. -/
def SecretBlocks {E : Type} [Fintype E] {l m : ℕ}
    (s : Fin m → Op (Fin l × E)) (eps : ℝ) : Prop :=
  ∃ eta : Fin m → Op (Fin l × E), ∃ sigma : Op (Fin l × E),
    QAlgorithms.IsDensityMatrix sigma ∧
    ∀ k, QAlgorithms.IsDensityMatrix (eta k) ∧
      ((s k).trace.re : ℂ) • eta k = s k ∧
      QAlgorithms.traceNorm (eta k - sigma) ≤ eps

/-- PDF p.2: all three key criteria, with the full l1 distance from uniform. -/
def KeyGood {E : Type} [Fintype E] {l m : ℕ}
    (joint : Fin m → Fin m → ℝ) (s : Fin m → Op (Fin l × E)) (eps : ℝ) : Prop :=
  (∑ k, ∑ j, if k ≠ j then joint k j else 0) ≤ eps ∧
    (∑ k, |(s k).trace.re - (m : ℝ)⁻¹|) ≤ eps ∧ SecretBlocks s eps

/-- PDF p.2: finite cqq one-way protocol on n copies. Alice uses a stochastic
map X^n -> (public transcript,key); Bob's POVM depends only on that transcript. -/
structure CqqProtocol (X B : Type) (n : ℕ) where
  l : ℕ
  m : ℕ
  encode : (Fin n → X) → Fin l × Fin m → ℝ
  decode : Fin l → Fin m → Op (Fin n → B)

/-- PDF p.2: precisely the legal cqq encoding and decoding operations. -/
def CqqProtocol.Valid {X B : Type} [Fintype B] {n : ℕ}
    (P : CqqProtocol X B n) : Prop :=
  0 < P.l ∧ 0 < P.m ∧ IsStochastic P.encode ∧
    ∀ t, QAlgorithms.IsPOVM (P.decode t)

/-- PDF p.2: the actual joint key law after the protocol. -/
def CqqProtocol.joint {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    {n : ℕ} (P : CqqProtocol X B n) (p : X → ℝ) (W : X → Op (B × E))
    (k j : Fin P.m) : ℝ :=
  ∑ x, ∑ t, lawCopies p n x * P.encode x (t,k) *
    QAlgorithms.effectProb (P.decode t j)
      (channelWordState (fun a => QAlgorithms.traceRight (W a)) x)

/-- PDF p.2: Eve receives a classical copy of the public transcript. These
are unnormalized blocks indexed by Alice's key, after forgetting Bob's outcome. -/
def CqqProtocol.blocks {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    {n : ℕ} (P : CqqProtocol X B n) (p : X → ℝ) (W : X → Op (B × E))
    (k : Fin P.m) : Op (Fin P.l × (Fin n → E)) :=
  fun y z => if y.1 = z.1 then
    ∑ x, ((lawCopies p n x * P.encode x (y.1,k) : ℝ) : ℂ) *
      channelWordState (fun a => QAlgorithms.traceLeft (W a)) x y.2 z.2 else 0

/-- PDF p.2: an evaluated sequence with errors tending to zero and ONE finite
public-rate bound F for every block length. The sequence exists for every n,
including a harmless zero-copy member. -/
def CqqAchieves {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    (p : X → ℝ) (W : X → Op (B × E))
    (P : (n : ℕ) → CqqProtocol X B n) (rate : ℝ) : Prop :=
  ∃ eps : ℕ → ℝ, ∃ F : ℝ, 0 ≤ F ∧
    (∀ n, 0 ≤ eps n ∧ (P n).Valid ∧
      KeyGood ((P n).joint p W) ((P n).blocks p W) (eps n) ∧
      ((P n).l : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * F)) ∧
    Tendsto eps atTop (nhds 0) ∧
    Tendsto (fun n => Real.logb 2 ((P n).m : ℝ) / n) atTop (nhds rate)

/-- PDF p.2: operational forward secret-key capacity; no entropic substitute. -/
def cqqKeyCapacity {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    (p : X → ℝ) (W : X → Op (B × E)) : ℝ :=
  sSup {r | ∃ P : (n : ℕ) → CqqProtocol X B n, CqqAchieves p W P r}

/-- PDF pp.5--6: finite general-state one-way key protocol. Alice measures
Q_(transcript,key) and Bob measures conditional on the authenticated transcript. -/
structure QuantumKeyProtocol (A B : Type) (n : ℕ) where
  l : ℕ
  m : ℕ
  measure : Fin l × Fin m → Op (Fin n → A)
  decode : Fin l → Fin m → Op (Fin n → B)

/-- PDF p.6: all finite POVMs on Alice are allowed, without a purity assumption. -/
def QuantumKeyProtocol.Valid {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : QuantumKeyProtocol A B n) : Prop :=
  0 < P.l ∧ 0 < P.m ∧ QAlgorithms.IsPOVM P.measure ∧
    ∀ t, QAlgorithms.IsPOVM (P.decode t)

/-- PDF p.5: the UNNORMALIZED conditional BE block of a POVM outcome.
This is Tr_A(rho (Q tensor I)); there is no additional factor P(x). -/
def measuredBlock {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (rho : Op (A × (B × E))) (Q : Op A) : Op (B × E) :=
  QAlgorithms.traceLeft (rho * Matrix.kronecker Q (1 : Op (B × E)))

/-- PDF p.6: the physically evaluated joint law of Alice and Bob's keys. -/
def QuantumKeyProtocol.joint {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    {n : ℕ} (P : QuantumKeyProtocol A B n) (rho : Op (A × (B × E)))
    (k j : Fin P.m) : ℝ :=
  ∑ t, QAlgorithms.effectProb (P.decode t j)
    (QAlgorithms.traceRight (measuredBlock (triCopies rho n) (P.measure (t,k))))

/-- PDF pp.5--6: Eve's evaluated public-transcript blocks, diagonal in transcript. -/
def QuantumKeyProtocol.blocks {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    {n : ℕ} (P : QuantumKeyProtocol A B n) (rho : Op (A × (B × E)))
    (k : Fin P.m) : Op (Fin P.l × (Fin n → E)) :=
  fun y z => if y.1 = z.1 then
    QAlgorithms.traceLeft (measuredBlock (triCopies rho n) (P.measure (y.1,k))) y.2 z.2
    else 0

/-- PDF p.6: operational general-state secret-key sequences, using all three
p.2 criteria and one fixed finite F before n. -/
def QuantumKeyAchieves {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (rho : Op (A × (B × E))) (P : (n : ℕ) → QuantumKeyProtocol A B n)
    (rate : ℝ) : Prop :=
  ∃ eps : ℕ → ℝ, ∃ F : ℝ, 0 ≤ F ∧
    (∀ n, 0 ≤ eps n ∧ (P n).Valid ∧
      KeyGood ((P n).joint rho) ((P n).blocks rho) (eps n) ∧
      ((P n).l : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * F)) ∧
    Tendsto eps atTop (nhds 0) ∧
    Tendsto (fun n => Real.logb 2 ((P n).m : ℝ) / n) atTop (nhds rate)

/-- PDF pp.5--6: the general-state forward key capacity, defined operationally. -/
def quantumKeyCapacity {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (rho : Op (A × (B × E))) : ℝ :=
  sSup {r | ∃ P : (n : ℕ) → QuantumKeyProtocol A B n, QuantumKeyAchieves rho P r}

/-- PDF p.5: the unnormalized (u,t) BE blocks of X -> U -> T. -/
def processedBlocks {X B E : Type} [Fintype X] {u t : ℕ}
    (p : X → ℝ) (W : X → Op (B × E)) (Q : X → Fin u → ℝ)
    (R : Fin u → Fin t → ℝ) (i : Fin u) (j : Fin t) : Op (B × E) :=
  ∑ x, ((R i j * Q x i * p x : ℝ) : ℂ) • W x

/-- PDF p.5: I(U;B|T)-I(U;E|T), evaluated from unnormalized joint blocks.
Every zero-mass branch is weighted by zero after choosing a normalized version. -/
def conditionalAdvantage {B E : Type} [Fintype B] [Fintype E] {u t : ℕ}
    (v : Fin u → Fin t → Op (B × E)) : ℝ :=
  (∑ j, let s := ∑ i, v i j
    s.trace.re * (QAlgorithms.vnEntropy (QAlgorithms.traceRight (normalized s)) -
      QAlgorithms.vnEntropy (QAlgorithms.traceLeft (normalized s)))) -
  ∑ i, ∑ j, (v i j).trace.re *
    (QAlgorithms.vnEntropy (QAlgorithms.traceRight (normalized (v i j))) -
      QAlgorithms.vnEntropy (QAlgorithms.traceLeft (normalized (v i j))))

/-- PDF p.5: the UNRESTRICTED classical preprocessing objective values. -/
def cqqValues {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    (p : X → ℝ) (W : X → Op (B × E)) : Set ℝ :=
  {v | ∃ u t : ℕ, 0 < u ∧ 0 < t ∧
    ∃ Q : X → Fin u → ℝ, ∃ R : Fin u → Fin t → ℝ,
      IsStochastic Q ∧ IsStochastic R ∧ v = conditionalAdvantage (processedBlocks p W Q R)}

/-- PDF p.5: single-copy key optimization, independently of operational rates.
Theorem 6 asserts that this supremum is a maximum with the printed range bounds. -/
def cqqSingle {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    (p : X → ℝ) (W : X → Op (B × E)) : ℝ := sSup (cqqValues p W)

/-- PDF p.5: measured-state (x,t) blocks. Printed redundant P(x) is omitted. -/
def quantumProcessed {A B E : Type} [Fintype A] [Fintype B] [Fintype E] {x t : ℕ}
    (rho : Op (A × (B × E))) (Q : Fin x → Op A) (R : Fin x → Fin t → ℝ)
    (i : Fin x) (j : Fin t) : Op (B × E) :=
  (R i j : ℂ) • measuredBlock rho (Q i)

/-- PDF p.5: unrestricted finite POVM and classical T|X objective values. -/
def quantumKeyValues {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (rho : Op (A × (B × E))) : Set ℝ :=
  {v | ∃ x t : ℕ, 0 < x ∧ 0 < t ∧
    ∃ Q : Fin x → Op A, ∃ R : Fin x → Fin t → ℝ,
      QAlgorithms.IsPOVM Q ∧ IsStochastic R ∧
      v = conditionalAdvantage (quantumProcessed rho Q R)}

/-- PDF p.5: general-state single-copy key objective. -/
def quantumKeySingle {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (rho : Op (A × (B × E))) : ℝ := sSup (quantumKeyValues rho)

/-- PDF p.6: finite quantum instrument with arbitrary output dimension and
unobserved Kraus index; the classical branch is l. This is raw rectangular data
on arbitrary register types, with validity checked separately. Accepted P08.Instrument
uses Fin dimensions and bundles completeness; Nonconvex.Instrument has square
continuous-linear maps with norm completeness. Neither is this data interface. -/
structure RectangularKrausData (A C : Type) where
  l : ℕ
  k : ℕ
  kraus : Fin l → Fin k → Matrix C A ℂ

/-- PDF p.6: the CP branches sum to a trace-preserving map. -/
def RectangularKrausData.Valid {A C : Type} [Fintype C] (T : RectangularKrausData A C) : Prop :=
  0 < T.l ∧ ∑ i, ∑ j, (T.kraus i j)ᴴ * T.kraus i j = 1

/-- PDF p.9: a branch applied to the ACTUAL input, identity on Bob. -/
def RectangularKrausData.branch {A B C : Type} [Fintype A] [Fintype B]
    (T : RectangularKrausData A C) (rho : Op (A × B)) (i : Fin T.l) : Op (C × B) :=
  ∑ j, let K := Matrix.kronecker (T.kraus i j) (1 : Op B)
    K * rho * Kᴴ

/-- PDF p.6: Bob's arbitrary finite-dimensional CPTP map in Kraus form. -/
structure BobChannel (B D : Type) where
  k : ℕ
  kraus : Fin k → Matrix D B ℂ

/-- PDF p.6: completeness of Bob's local Kraus family. -/
def BobChannel.Valid {B D : Type} [Fintype D] (R : BobChannel B D) : Prop :=
  QAlgorithms.IsKrausFamily R.kraus

/-- PDF p.6: a one-way EPR protocol. Alice outputs on the M-dimensional
target support; the only shared input is the supplied n-copy state. -/
structure EntProtocol (A B : Type) (n : ℕ) where
  m : ℕ
  alice : RectangularKrausData (Fin n → A) (Fin m)
  bob : Fin alice.l → BobChannel (Fin n → B) (Fin m)

/-- PDF p.6: legality of the instrument and every transcript-dependent Bob map. -/
def EntProtocol.Valid {A B : Type} {n : ℕ} (P : EntProtocol A B n) : Prop :=
  0 < P.m ∧ P.alice.Valid ∧ ∀ i, (P.bob i).Valid

/-- PDF p.6: branch-averaged output sum_l (T_l tensor R_l)(rho^n). -/
def EntProtocol.output {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : EntProtocol A B n) (rho : Op (A × B)) : Op (Fin P.m × Fin P.m) :=
  ∑ i, ∑ j, ∑ k,
    let K := Matrix.kronecker (P.alice.kraus i j) ((P.bob i).kraus k)
    K * bipCopies rho n * Kᴴ

/-- PDF pp.6,12: squared fidelity with the pure EPR target. -/
def eprFidelity {m : ℕ} (s : Op (Fin m × Fin m)) : ℝ :=
  (∑ a, ∑ b,
    conj (QAlgorithms.Papers.Independent.Information100.P22.bell (Fin m) a) * s a b *
      QAlgorithms.Papers.Independent.Information100.P22.bell (Fin m) b).re

/-- PDF p.6: a fixed protocol sequence attaining a rate; no good coherent
protocol is assumed as a theorem hypothesis. Classical cost is log l. -/
def EntAchieves {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B))
    (P : (n : ℕ) → EntProtocol A B n) (rate : ℝ) : Prop :=
  (∀ n, (P n).Valid) ∧
    Tendsto (fun n => eprFidelity ((P n).output rho)) atTop (nhds 1) ∧
    Tendsto (fun n => Real.logb 2 ((P n).m : ℝ) / n) atTop (nhds rate)

/-- PDF p.6: the one-way EPR capacity, defined through evaluated protocols. -/
def entCapacity {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) : ℝ :=
  sSup {r | ∃ P : (n : ℕ) → EntProtocol A B n, EntAchieves rho P r}

/-- PDF p.7: coherent information I_c(A>B). -/
def coherentInfo {A B : Type} [Fintype A] [Fintype B] (s : Op (A × B)) : ℝ :=
  QAlgorithms.vnEntropy (QAlgorithms.traceLeft s) - QAlgorithms.vnEntropy s

/-- PDF p.9: the weighted normalized-branch objective of a genuine instrument. -/
def instrumentYield {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (rho : Op (A × B)) (T : RectangularKrausData A C) : ℝ :=
  ∑ i, (T.branch rho i).trace.re * coherentInfo (normalized (T.branch rho i))

/-- PDF p.9: unrestricted objective values, allowing arbitrary finite Alice output. -/
def entValues {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) : Set ℝ :=
  {v | ∃ c : ℕ, 0 < c ∧ ∃ T : RectangularKrausData A (Fin c), T.Valid ∧
    v = instrumentYield rho T}

/-- PDF p.9: single-copy instrument optimization. Attainment is a theorem. -/
def entSingle {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) : ℝ :=
  sSup (entValues rho)

/-- PDF p.9: the square, single-Kraus instrument used by the restricted optimizer. -/
def squareInstrument {A : Type} {l : ℕ} (V : Fin l → Op A) : RectangularKrausData A A :=
  ⟨l,1,fun i _ => V i⟩

/-- PDF p.8: the AE marginal of a tripartite state, tracing only Bob. -/
def marginalAE {A B E : Type} [Fintype B] (s : Op (A × (B × E))) : Op (A × E) :=
  fun y z => ∑ b, s (y.1,(b,y.2)) (z.1,(b,z.2))

/-- PDF p.8: mutual information I(A:E) of a fixed purification. -/
def mutualAE {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (s : Op (A × (B × E))) : ℝ :=
  QAlgorithms.vnEntropy (QAlgorithms.traceRight s) +
    QAlgorithms.vnEntropy (QAlgorithms.traceLeft (QAlgorithms.traceLeft s)) -
    QAlgorithms.vnEntropy (marginalAE s)

/-- PDF pp.8--9: Bell convention Phi_00=Phi+, Phi_01=Phi-,
Phi_10=Psi+, Phi_11=Psi-. Bits are Bool, false=0, true=1. Obtained by bit/phase flips of the accepted
maximally entangled vector, rather than re-declaring it. -/
def pauliBellVector (i j : Bool) : Vec (Bool × Bool) :=
  WithLp.toLp 2 fun z =>
    QAlgorithms.Papers.Independent.Information100.P22.bell Bool
      (z.1, Bool.xor z.2 i) * (if j && z.1 then -1 else 1)

/-- PDF p.8: manifestly normalized Bell-sum purification. This avoids the
printed 1/sqrt(1) typo in the subsequent Schmidt expression. -/
def bellPurification (p : Bool × Bool → ℝ) : Vec (Bool × (Bool × (Bool × Bool))) :=
  WithLp.toLp 2 fun z => (Real.sqrt (p z.2.2) : ℂ) *
    pauliBellVector z.2.2.1 z.2.2.2 (z.1,z.2.1)

/-- PDF p.9: normalized BE states conditional on Alice's computational outcome.
The outcome probabilities are exactly 1/2, including rank-deficient mixtures. -/
def bellConditional (p : Bool × Bool → ℝ) (x : Bool) : Op (Bool × (Bool × Bool)) :=
  QAlgorithms.pureDensity (WithLp.toLp 2 fun z =>
    (Real.sqrt 2 : ℂ) * bellPurification p (x,z))

/-- PDF p.9: the bit-flip distribution p_00+p_01, p_10+p_11. -/
def bellBitLaw (p : Bool × Bool → ℝ) (i : Bool) : ℝ := ∑ j, p (i,j)

/-- PDF p.10: regroup n copies into the finite-dimensional interface of the
accepted finite-LOCC semantics, using the canonical finite-function equivalence. -/
def finBipCopies {a b : ℕ} (rho : Op (Fin a × Fin b)) (n : ℕ) :
    Op (Fin (a^n) × Fin (b^n)) :=
  fun y z => bipCopies rho n
    (finFunctionFinEquiv.symm y.1,finFunctionFinEquiv.symm y.2)
    (finFunctionFinEquiv.symm z.1,finFunctionFinEquiv.symm z.2)

/-- PDF p.10: actual two-way LOCC output coherent-information values. Arbitrary
finite positive output dimensions and unbounded finite round counts are allowed;
the supremum includes approximation by finite protocols, without attainment. -/
def twoWayValues {a b : ℕ} (rho : Op (Fin a × Fin b)) (n : ℕ) : Set ℝ :=
  {v | ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∃ V : QAlgorithms.Superop (Fin (a^n) × Fin (b^n)) (Fin c × Fin d),
      QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC V ∧
      v = coherentInfo (V (finBipCopies rho n))}

/-- PDF p.10: optimized coherent information after evaluated two-way LOCC. -/
def twoWaySingle {a b : ℕ} (rho : Op (Fin a × Fin b)) (n : ℕ) : ℝ :=
  sSup (twoWayValues rho n)

/-- PDF pp.9--10: two-way EPR rate using genuine finite LOCC, evaluated on the
independent-copy input. Local environments may be discarded, no shared ancilla
is supplied, and approximation is expressed by EPR fidelity tending to one. -/
def TwoWayAchievable {a b : ℕ} (rho : Op (Fin a × Fin b)) (rate : ℝ) : Prop :=
  ∃ m : ℕ → ℕ,
    ∃ V : (n : ℕ) → QAlgorithms.Superop (Fin (a^n) × Fin (b^n)) (Fin (m n) × Fin (m n)),
      (∀ n, 0 < m n ∧
        QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC (V n)) ∧
      Tendsto (fun n => eprFidelity (V n (finBipCopies rho n))) atTop (nhds 1) ∧
      Tendsto (fun n => Real.logb 2 (m n : ℝ) / n) atTop (nhds rate)

/-- PDF p.10: operational two-way EPR distillable entanglement. -/
def twoWayCapacity {a b : ℕ} (rho : Op (Fin a × Fin b)) : ℝ :=
  sSup {r | TwoWayAchievable rho r}

/-- PDF p.5, Theorem 6: a maximum of the unrestricted objective, attained
with |T|<=|X|, |U|<=|X|^2 and deterministic T=f(U). -/
def CqqRestrictedMaximum {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    (p : X → ℝ) (W : X → Op (B × E)) : Prop :=
  ∃ u t : ℕ, 0 < u ∧ 0 < t ∧ u ≤ (Fintype.card X)^2 ∧ t ≤ Fintype.card X ∧
    ∃ Q : X → Fin u → ℝ, ∃ f : Fin u → Fin t, IsStochastic Q ∧
      IsGreatest (cqqValues p W) (conditionalAdvantage
        (processedBlocks p W Q (fun i j => if j = f i then 1 else 0)))

/-- PDF pp.5,15, Theorem 8: attainment of the unrestricted POVM objective
with |T|<=d_A^2, |X|<=d_A^4 and deterministic T=f(X). -/
def QuantumRestrictedMaximum {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (rho : Op (A × (B × E))) : Prop :=
  ∃ x t : ℕ, 0 < x ∧ 0 < t ∧ x ≤ (Fintype.card A)^4 ∧ t ≤ (Fintype.card A)^2 ∧
    ∃ Q : Fin x → Op A, ∃ f : Fin x → Fin t, QAlgorithms.IsPOVM Q ∧
      IsGreatest (quantumKeyValues rho) (conditionalAdvantage
        (quantumProcessed rho Q (fun i j => if j = f i then 1 else 0)))

/-- PDF p.9: unrestricted instrument optimization is attained by a square
positive single-Kraus instrument on the original Alice space, with L<=d_A^2. -/
def EntRestrictedMaximum {A B : Type} [Fintype A] [Fintype B]
    (rho : Op (A × B)) : Prop :=
  ∃ l : ℕ, 0 < l ∧ l ≤ (Fintype.card A)^2 ∧ ∃ V : Fin l → Op A,
    (∀ i, (V i).PosSemidef) ∧ (∑ i, (V i)ᴴ * V i) = 1 ∧
      IsGreatest (entValues rho) (instrumentYield rho (squareInstrument V))

/-- PDF p.2: quantum mutual information for a bipartite state. -/
def quantumMutualInfo {A B : Type} [Fintype A] [Fintype B] (s : Op (A × B)) : ℝ :=
  QAlgorithms.vnEntropy (QAlgorithms.traceRight s) +
    QAlgorithms.vnEntropy (QAlgorithms.traceLeft s) - QAlgorithms.vnEntropy s

/-- PDF pp.6,8: four-Bell-state mixture with the paper's Bell numbering.
Distinct from accepted Dependency50.P36.bellMixture, a one-parameter mixture
of only two Bell states on Fin 2 registers. -/
def bellDiagonalState (p : Bool × Bool → ℝ) : Op (Bool × Bool) :=
  ∑ i, (p i : ℂ) • QAlgorithms.pureDensity (pauliBellVector i.1 i.2)

/-- PDF pp.8--9: an attained entanglement rate together with two public message
components on the SAME protocol sequence. The instrument's l outcomes identify
Fin(code_n) x Fin(phase_n), so the component cardinalities describe real messages. -/
def EntSplitAttains {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B))
    (rate codeCost phaseCost : ℝ) : Prop :=
  ∃ P : (n : ℕ) → EntProtocol A B n, EntAchieves rho P rate ∧
    ∃ code phase : ℕ → ℕ,
      (∀ n, 0 < code n ∧ 0 < phase n ∧ (P n).alice.l = code n * phase n) ∧
      Tendsto (fun n => Real.logb 2 (code n : ℝ) / n) atTop (nhds codeCost) ∧
      Tendsto (fun n => Real.logb 2 (phase n : ℝ) / n) atTop (nhds phaseCost)

/-! Sanity checks pin product order, zero-copy values, public transcript
classicality, branch evaluation, EPR normalization and the Bell sign convention.
They do not prove the paper's results. -/

example {X : Type} (p : X → ℝ) (x : Fin 0 → X) : lawCopies p 0 x = 1 := by
  simp [lawCopies]

example {X H : Type} (W : X → Op H) (x : Fin 1 → X) (y z : Fin 1 → H) :
    channelWordState W x y z = W (x 0) (y 0) (z 0) := by simp [channelWordState, QAlgorithms.Papers.Independent.Dependency50.P07.wordState]

example {A B : Type} (rho : Op (A × B))
    (y z : (Fin 0 → A) × (Fin 0 → B)) : bipCopies rho 0 y z = 1 := by
  simp [bipCopies]

example {A B E : Type} (rho : Op (A × (B × E)))
    (y z : (Fin 0 → A) × ((Fin 0 → B) × (Fin 0 → E))) :
    triCopies rho 0 y z = 1 := by simp [triCopies]

example {X : Type} [Fintype X] (p : X → ℝ) : shannon p = -∑ x, p x * Real.logb 2 (p x) := rfl

example {A : Type} [Fintype A] : normalized (0 : Op A) = ((Fintype.card A : ℂ)⁻¹) • 1 := by
  simp [normalized]

example : QAlgorithms.Papers.Independent.Information100.P22.bell (Fin 1) (0,0) = 1 := by simp [QAlgorithms.Papers.Independent.Information100.P22.bell]

example : pauliBellVector false false (false,true) = 0 := by simp [pauliBellVector, QAlgorithms.Papers.Independent.Information100.P22.bell]

example : pauliBellVector false true (true,true) = -((Real.sqrt 2)⁻¹ : ℂ) := by simp [pauliBellVector, QAlgorithms.Papers.Independent.Information100.P22.bell]

example {A : Type} {l : ℕ} (V : Fin l → Op A) (i : Fin l) :
    (squareInstrument V).kraus i ⟨0, by simp [squareInstrument]⟩ = V i := rfl

example {E : Type} [Fintype E] {l m : ℕ}
    (s : Fin m → Op (Fin l × E)) (eps : ℝ) (h : SecretBlocks s eps) :
    ∃ eta : Fin m → Op (Fin l × E), ∃ sigma : Op (Fin l × E),
      QAlgorithms.IsDensityMatrix sigma ∧ ∀ k, QAlgorithms.IsDensityMatrix (eta k) ∧
      ((s k).trace.re : ℂ) • eta k = s k ∧ QAlgorithms.traceNorm (eta k - sigma) ≤ eps := h

example : IsLaw (fun _ : Unit => (1 : ℝ)) := by
  simp [IsLaw]

example {X : Type} : IsStochastic (fun _ : X => fun _ : Unit => (1 : ℝ)) := by
  simp [IsStochastic, IsLaw]

example {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (rho : Op (A × (B × E))) : measuredBlock rho 0 = 0 := by
  ext b b2
  simp [measuredBlock, QAlgorithms.traceLeft]

example {B E : Type} [Fintype B] [Fintype E] {t : ℕ}
    (v : Fin 0 → Fin t → Op (B × E)) : conditionalAdvantage v = 0 := by
  simp [conditionalAdvantage]

example {A B C : Type} [Fintype A] [Fintype B]
    (T : RectangularKrausData A C) (i : Fin T.l) : T.branch (0 : Op (A × B)) i = 0 := by
  simp [RectangularKrausData.branch]

example {m : ℕ} : eprFidelity (0 : Op (Fin m × Fin m)) = 0 := by
  simp [eprFidelity]

example {X B E : Type} [Fintype X] [Fintype B] [Fintype E] {n : ℕ}
    (P : CqqProtocol X B n) (p : X → ℝ) (W : X → Op (B × E))
    (k : Fin P.m) (y z : Fin P.l × (Fin n → E)) (h : y.1 ≠ z.1) :
    P.blocks p W k y z = 0 := by simp [CqqProtocol.blocks, h]

example {A B E : Type} [Fintype A] [Fintype B] [Fintype E] {n : ℕ}
    (P : QuantumKeyProtocol A B n) (rho : Op (A × (B × E)))
    (k : Fin P.m) (y z : Fin P.l × (Fin n → E)) (h : y.1 ≠ z.1) :
    P.blocks rho k y z = 0 := by simp [QuantumKeyProtocol.blocks, h]

example {X B E : Type} (W : X → Op (B × E)) (x : Fin 1 → X)
    (y z : (Fin 1 → B) × (Fin 1 → E)) :
    cqqCopies W x y z = W (x 0) (y.1 0,y.2 0) (z.1 0,z.2 0) := by
  simp [cqqCopies]

end QAlgorithms.Papers.Independent.Frontier30.P12


