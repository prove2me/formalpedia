-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20
-- name    : QAlgorithms_Papers_Independent_Support50_P20
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T20:28:33.817+00:00
-- url     : https://prove2.me/theorems/6ff03287-8574-4b34-be86-ba0f4c133126
-- title:
--   Definitions for One-Shot Classical-Quantum Capacity and Hypothesis Testing
-- statement:
--   The objects the formalized statements of *One-Shot Classical-Quantum Capacity and Hypothesis Testing* (arXiv:1007.5456) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsBinaryEffect`: PDF p.2, (1): a bounded binary effect; singular effects are allowed.
--   - `Effect`: PDF p.2: all bounded binary effects on the output space.
--   - `traceAcceptance`: PDF p.2, (1): the actual trace pairing Tr(Q rho). The product of a bounded operator with a trace-class operator is trace class, so the basis trace converges.
--   - `negativeLogTwo`: PDF p.2, (1): extended negative logarithm, including -log2(0)=+infinity. The infinity branch is included for totality; testing beta is finite on states at the error parameters used by the statements.
--   - `hilbertTestingBeta`: PDF p.2, (1): infimum of type-II acceptance over all feasible bounded tests. The extended infimum of an empty set is infinity. For states and epsilon>=0, I is feasible and every objective lies in [0,1].
--   - `hilbertTestingDivergence`: PDF p.2, (1): unnormalized hypothesis-testing divergence in bits.
--   - `closedSupportProjector`: PDF p.2: support of a positive operator is the orthogonal complement of its kernel, a closed subspace. The projection is not an inverse or matrix power.
--   - `orderZeroDivergence`: PDF p.2: order-zero Renyi divergence with the actual closed-support projector.
--   - `traceClassRelativeEntropyBits`: PDF p.2, (2): Umegaki relative entropy in bits. The accepted extended finite-compression formula includes the trace correction on subnormalized compressions and infinity on support failure. No entropy-finiteness premise.
--   - `PositiveHilbertBlock`: PDF p.2, DPI: positivity of an actual finite operator block matrix.
--   - `IsHilbertCPTP`: PDF p.2, DPI and its proof: physical preprocessing means complex linear, trace-preserving and completely positive on trace class. All finite matrix amplifications are required, with no Kraus-rank bound. Off-domain values are unused. Printed: CPM. Convention: CPTP, as required by the proof's measurement pullback.
--   - `ClassicalInputChannel`: PDF pp.1–2: an arbitrary cq channel on a nonempty input set (the Nonempty instance is imposed by each capacity statement). Its outputs are actual densities.
--   - `cqJointAcceptance`: PDF p.2, Theorem 1: Tr(Q piAB), computed from the diagonal classical blocks Q_x = (<x| tensor I) Q (|x> tensor I). Every family of effects has a direct-sum realization, and the omitted off-diagonal blocks never affect either cq trace.
--   - `cqProductAcceptance`: PDF p.2, Theorem 1: Tr(Q (piA tensor piB)), with actual marginals piA=diag(P), piB=sum_y P(y)rho_y. Both sums converge absolutely: the trace pairings are in [0,1] and the PMF weights sum to one.
--   - `cqTestingBeta`: PDF p.2, (1),(3): type-II optimization for the cq pair in its exact diagonal-block representation. No finite-support restriction on P is imposed.
--   - `cqTestingInformation`: PDF p.2, (3): hypothesis-testing information of the constructed cq pair.
--   - `optimizedTestingInformation`: PDF p.2, (3): supremum over all discrete input distributions; extended suprema preserve unbounded channel information.
--   - `ClassicalMessageCode`: PDF p.2: an actual m-message code. Repeated codewords and zero POVM elements are allowed. Completeness holds on the entire output space.
--   - `uniformDecodingError`: PDF p.2: average error with uniformly distributed messages.
--   - `finiteMessageRate`: PDF p.2: rate is log2(m) for a positive integer message count.
--   - `oneUseCodeCapacity`: PDF p.2, Theorem 1: operational one-shot capacity, defined independently from testing information. An unbounded channel has capacity +infinity.
--   - `BlockHilbert`: PDF p.4, (10): B tensor (n+1) in completed Hilbert coordinates. The zero sequence index denotes one channel use; every rate denominator is positive.
--   - `blockBasis`: PDF p.4: canonical orthonormal tensor-product basis of the output block.
--   - `vanishingErrorCapacity`: PDF p.4, (10): independent operational capacity from actual sequences of codes with error tending to zero and their lower limiting rates. There is no compatibility, causality, stationarity or product-input assumption on W.
-- source:
--   One-Shot Classical-Quantum Capacity and Hypothesis Testing, arXiv:1007.5456v3, https://arxiv.org/abs/1007.5456v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

/-!
# One-shot classical-quantum capacity and hypothesis testing

Wang and Renner, arXiv:1007.5456v3. Page references are PDF pages.
All output Hilbert spaces may be infinite dimensional and nonseparable.
The accepted State, nuclear trace-class, base-two logarithm, and extended
relative-entropy definitions are reused without changing their bodies. Local
operator/code interfaces have distinct names because the same-name frozen
interfaces have different types or operational tasks (see ASSESSMENT.json).
The cq pair is represented by its exact
trace contractions against diagonal test blocks: off-diagonal classical blocks
contribute to neither acceptance probability, and every family of effects is
realized by a bounded direct-sum effect. Thus this representation optimizes all
binary tests, without restricting the alphabet or the distribution support.

Equation (7), as a single finite-code existence claim for an unbounded channel,
and the unspecified computational claim after (1), are deferred in HARD.md.
Compilation is pending the batch handoff.
-/

noncomputable section

open Filter
open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.2, (1): a bounded binary effect; singular effects are allowed. -/
def IsBinaryEffect (Q : H →L[ℂ] H) : Prop :=
  IsPositive Q ∧ IsPositive (1 - Q)

/-- PDF p.2: all bounded binary effects on the output space. -/
abbrev Effect (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] := {Q : H →L[ℂ] H // IsBinaryEffect Q}

/-- PDF p.2, (1): the actual trace pairing Tr(Q rho). The product of a bounded
operator with a trace-class operator is trace class, so the basis trace converges. -/
def traceAcceptance {I : Type*} (b : HilbertBasis I ℂ H)
    (Q rho : H →L[ℂ] H) : ℝ :=
  (operatorTrace b (Q.comp rho)).re

/-- PDF p.2, (1): extended negative logarithm, including -log2(0)=+infinity.
The infinity branch is included for totality; testing beta is finite on states
at the error parameters used by the statements. -/
def negativeLogTwo (x : ℝ≥0∞) : EReal :=
  if x = 0 then ⊤ else if x = ⊤ then ⊥ else (-logTwo x.toReal : ℝ)

/-- PDF p.2, (1): infimum of type-II acceptance over all feasible bounded tests.
The extended infimum of an empty set is infinity. For states and epsilon>=0,
I is feasible and every objective lies in [0,1]. -/
def hilbertTestingBeta {I : Type*} (b : HilbertBasis I ℂ H) (epsilon : ℝ)
    (rho sigma : H →L[ℂ] H) : ℝ≥0∞ :=
  sInf {z | ∃ Q : Effect H,
    1 - epsilon ≤ traceAcceptance b Q.val rho ∧
    z = ENNReal.ofReal (traceAcceptance b Q.val sigma)}

/-- PDF p.2, (1): unnormalized hypothesis-testing divergence in bits. -/
def hilbertTestingDivergence {I : Type*} (b : HilbertBasis I ℂ H) (epsilon : ℝ)
    (rho sigma : H →L[ℂ] H) : EReal :=
  negativeLogTwo (hilbertTestingBeta b epsilon rho sigma)

/-- PDF p.2: support of a positive operator is the orthogonal complement of
its kernel, a closed subspace. The projection is not an inverse or matrix power. -/
def closedSupportProjector (rho : H →L[ℂ] H) : H →L[ℂ] H :=
  (LinearMap.ker rho.toLinearMap)ᗮ.starProjection

/-- PDF p.2: order-zero Renyi divergence with the actual closed-support projector. -/
def orderZeroDivergence {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) : EReal :=
  negativeLogTwo (ENNReal.ofReal (traceAcceptance b (closedSupportProjector rho) sigma))

/-- PDF p.2, (2): Umegaki relative entropy in bits. The accepted extended
finite-compression formula includes the trace correction on subnormalized
compressions and infinity on support failure. No entropy-finiteness premise. -/
def traceClassRelativeEntropyBits {I : Type*} {b : HilbertBasis I ℂ H}
    (rho sigma : State b) : ℝ≥0∞ :=
  QAlgorithms.Papers.Independent.Dependency50.P13.relativeEntropy rho.val sigma.val /
    ENNReal.ofReal (Real.log 2)

/-- PDF p.2, DPI: positivity of an actual finite operator block matrix. -/
def PositiveHilbertBlock (n : ℕ) (A : Fin n → Fin n → (H →L[ℂ] H)) : Prop :=
  ∀ v : Fin n → H,
    (∑ i, ∑ j, inner ℂ (v i) (A i j (v j))).im = 0 ∧
    0 ≤ (∑ i, ∑ j, inner ℂ (v i) (A i j (v j))).re

/-- PDF p.2, DPI and its proof: physical preprocessing means complex linear,
trace-preserving and completely positive on trace class. All finite matrix
amplifications are required, with no Kraus-rank bound. Off-domain values are unused.
Printed: CPM. Convention: CPTP, as required by the proof's measurement pullback. -/
def IsHilbertCPTP {K J I : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (Phi : (H →L[ℂ] H) → (K →L[ℂ] K)) : Prop :=
  (∀ A B, IsTraceClass A → IsTraceClass B → Phi (A + B) = Phi A + Phi B) ∧
  (∀ (c : ℂ) A, IsTraceClass A → Phi (c • A) = c • Phi A) ∧
  (∀ A, IsTraceClass A →
    IsTraceClass (Phi A) ∧ operatorTrace d (Phi A) = operatorTrace b A) ∧
  ∀ n (A : Fin n → Fin n → (H →L[ℂ] H)),
    (∀ i j, IsTraceClass (A i j)) → PositiveHilbertBlock n A →
      PositiveHilbertBlock n (fun i j => Phi (A i j))

/-- PDF pp.1–2: an arbitrary cq channel on a nonempty input set (the Nonempty
instance is imposed by each capacity statement). Its outputs are actual densities. -/
abbrev ClassicalInputChannel (X : Type*) {I : Type*} (b : HilbertBasis I ℂ H) := X → State b

/-- PDF p.2, Theorem 1: Tr(Q piAB), computed from the diagonal classical blocks
Q_x = (<x| tensor I) Q (|x> tensor I). Every family of effects has a direct-sum
realization, and the omitted off-diagonal blocks never affect either cq trace. -/
def cqJointAcceptance {X I : Type*} (b : HilbertBasis I ℂ H)
    (W : ClassicalInputChannel X b) (P : PMF X) (Q : X → Effect H) : ℝ :=
  ∑' x, (P x).toReal * traceAcceptance b (Q x).val (W x).val.val

/-- PDF p.2, Theorem 1: Tr(Q (piA tensor piB)), with actual marginals
piA=diag(P), piB=sum_y P(y)rho_y. Both sums converge absolutely: the trace
pairings are in [0,1] and the PMF weights sum to one. -/
def cqProductAcceptance {X I : Type*} (b : HilbertBasis I ℂ H)
    (W : ClassicalInputChannel X b) (P : PMF X) (Q : X → Effect H) : ℝ :=
  ∑' x, (P x).toReal *
    (∑' y, (P y).toReal * traceAcceptance b (Q x).val (W y).val.val)

/-- PDF p.2, (1),(3): type-II optimization for the cq pair in its exact
diagonal-block representation. No finite-support restriction on P is imposed. -/
def cqTestingBeta {X I : Type*} (b : HilbertBasis I ℂ H)
    (W : ClassicalInputChannel X b) (P : PMF X) (epsilon : ℝ) : ℝ≥0∞ :=
  sInf {z | ∃ Q : X → Effect H,
    1 - epsilon ≤ cqJointAcceptance b W P Q ∧
    z = ENNReal.ofReal (cqProductAcceptance b W P Q)}

/-- PDF p.2, (3): hypothesis-testing information of the constructed cq pair. -/
def cqTestingInformation {X I : Type*} (b : HilbertBasis I ℂ H)
    (W : ClassicalInputChannel X b) (P : PMF X) (epsilon : ℝ) : EReal :=
  negativeLogTwo (cqTestingBeta b W P epsilon)

/-- PDF p.2, (3): supremum over all discrete input distributions; extended
suprema preserve unbounded channel information. -/
def optimizedTestingInformation {X I : Type*} (b : HilbertBasis I ℂ H)
    (W : ClassicalInputChannel X b) (epsilon : ℝ) : EReal :=
  ⨆ P : PMF X, cqTestingInformation b W P epsilon

/-- PDF p.2: an actual m-message code. Repeated codewords and zero POVM
elements are allowed. Completeness holds on the entire output space. -/
structure ClassicalMessageCode (X : Type*) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (m : ℕ) where
  positive : 0 < m
  word : Fin m → X
  decoder : Fin m → (H →L[ℂ] H)
  effect : ∀ i, IsBinaryEffect (decoder i)
  complete : ∑ i, decoder i = 1

/-- PDF p.2: average error with uniformly distributed messages. -/
def uniformDecodingError {X I : Type*} {m : ℕ} (b : HilbertBasis I ℂ H)
    (W : ClassicalInputChannel X b) (C : ClassicalMessageCode X H m) : ℝ :=
  1 - (m : ℝ)⁻¹ * ∑ i, traceAcceptance b (C.decoder i) (W (C.word i)).val.val

/-- PDF p.2: rate is log2(m) for a positive integer message count. -/
def finiteMessageRate (m : ℕ) : ℝ := logTwo m

/-- PDF p.2, Theorem 1: operational one-shot capacity, defined independently
from testing information. An unbounded channel has capacity +infinity. -/
def oneUseCodeCapacity {X I : Type*} (b : HilbertBasis I ℂ H)
    (W : ClassicalInputChannel X b) (epsilon : ℝ) : EReal :=
  sSup {r | ∃ (m : ℕ) (C : ClassicalMessageCode X H m),
    uniformDecodingError b W C ≤ epsilon ∧ r = (finiteMessageRate m : EReal)}

/-- PDF p.4, (10): B tensor (n+1) in completed Hilbert coordinates. The zero
sequence index denotes one channel use; every rate denominator is positive. -/
abbrev BlockHilbert (I : Type*) (n : ℕ) :=
  QAlgorithms.RealRegisters.Hilbert (Fin (n + 1) → I)

/-- PDF p.4: canonical orthonormal tensor-product basis of the output block. -/
def blockBasis (I : Type*) (n : ℕ) :
    HilbertBasis (Fin (n + 1) → I) ℂ (BlockHilbert I n) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- PDF p.4, (10): independent operational capacity from actual sequences of
codes with error tending to zero and their lower limiting rates. There is no
compatibility, causality, stationarity or product-input assumption on W. -/
def vanishingErrorCapacity {I : Type*} {X : ℕ → Type*}
    (W : ∀ n, ClassicalInputChannel (X n) (blockBasis I n)) : EReal :=
  sSup {r | ∃ (m : ℕ → ℕ) (C : ∀ n, ClassicalMessageCode (X n) (BlockHilbert I n) (m n)),
    Tendsto (fun n => uniformDecodingError (blockBasis I n) (W n) (C n)) atTop (nhds 0) ∧
    r = Filter.liminf (fun n => ((finiteMessageRate (m n) / (n + 1 : ℕ) : ℝ) : EReal)) atTop}

/-! Small sanity checks on definitions; no source theorem is proved here. -/

example : logTwo 1 = 0 := by simp [logTwo]

example : finiteMessageRate 1 = 0 := by simp [finiteMessageRate, logTwo]

example : negativeLogTwo 0 = ⊤ := by simp [negativeLogTwo]

example : negativeLogTwo ⊤ = ⊥ := by simp [negativeLogTwo]

example {I : Type*} (b : HilbertBasis I ℂ H) (rho : H →L[ℂ] H) :
    traceAcceptance b 0 rho = 0 := by simp [traceAcceptance, operatorTrace]

example {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b) :
    operatorTrace b rho.val.val = 1 := rho.property.2

example {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b) :
    traceAcceptance b 1 rho.val.val = 1 := by
  simpa only [traceAcceptance, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp, Complex.one_re] using congrArg Complex.re rho.property.2

example {X I : Type*} (b : HilbertBasis I ℂ H) (W : ClassicalInputChannel X b)
    (P : PMF X) (Q : X → Effect H) :
    cqJointAcceptance b W P Q =
      ∑' x, (P x).toReal * traceAcceptance b (Q x).val (W x).val.val := rfl

example : negativeLogTwo 1 = 0 := by simp [negativeLogTwo, logTwo]

example : closedSupportProjector (0 : H →L[ℂ] H) = 0 := by
  simp [closedSupportProjector]

example (n : ℕ) : PositiveHilbertBlock n (fun _ _ => (0 : H →L[ℂ] H)) := by
  intro v
  simp

example {I : Type*} (b : HilbertBasis I ℂ H) : IsHilbertCPTP b b id := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B hA hB
    rfl
  · intro c A hA
    rfl
  · intro A hA
    exact ⟨hA, rfl⟩
  · intro n A hA hPositive
    exact hPositive

example {X : Type*} (C : ClassicalMessageCode X H 0) : False :=
  (Nat.lt_irrefl 0) C.positive

end QAlgorithms.Papers.Independent.Support50.P20


