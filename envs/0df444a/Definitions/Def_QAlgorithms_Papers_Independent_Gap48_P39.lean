-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P39
-- name    : QAlgorithms_Papers_Independent_Gap48_P39
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T05:12:31.86406+00:00
-- url     : https://prove2.me/theorems/dd020f8a-ef80-46c4-85f8-20aeeda81531
-- title:
--   Definitions for Quantum broadcast channels
-- statement:
--   The objects the formalized statements of *Quantum broadcast channels* (arXiv:quant-ph/0603098) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CQChannel`: Classical-input broadcast channel, PDF p.2. Normalization excludes empty outputs.
--   - `CQChannel.word`: The actual memoryless product output for an input word, PDF p.4.
--   - `rank`: Source rank convention floor(2^(nR)), PDF p.4; at nonnegative rates it is positive.
--   - `NonnegativeTriple`: Nonnegative classical common/Bob/Charlie rates, PDF p.4.
--   - `NonnegativePair`: Nonnegative two-resource rates, with task-specific coordinate interpretation.
--   - `CQBroadcastCode`: Deterministic words and separate decoding POVMs, PDF p.4.
--   - `CQBroadcastCode.Good`: Joint maximum-error test, for EVERY message triple, PDF p.4.
--   - `cqBroadcastAchievable`: Vanishing maximum joint error at fixed rates; all sufficiently large positive n, PDF p.4.
--   - `cqBroadcastCapacity`: Operational CLOSED classical capacity, not an entropic definition, PDF p.4.
--   - `labelEntropy`: H(T) for a joint probability distribution, PDF pp.3–5.
--   - `cqTB`: The actual TB marginal of (14); weights stay subnormalized, including zero weights.
--   - `cqTC`: The actual TC marginal of (14), PDF p.4.
--   - `superpositionPrivateInfo`: I(X;B|T) in (14), using H(BT)-H(T)-sum p(t,x) H(B_x), PDF pp.4–5.
--   - `commonInfo`: I(T;C) in (14), PDF p.4.
--   - `totalInfo`: I(X;B) in (14), PDF p.4.
--   - `SuperpositionBounds`: The three simultaneous inequalities (13), without hiding the sum-rate bound.
--   - `superpositionCap`: Classical auxiliary cap, PDF pp.4,14; all physical output dimensions are positive.
--   - `superpositionRegion`: Classical auxiliary union; `none` allows every finite auxiliary, PDF p.4.
--   - `Degraded`: Source degradedness involves marginal channels, not a recovery map for BC, PDF pp.2,4.
--   - `CommutingBob`: Bob marginal commutation only, PDF p.4.
--   - `QuantumAux`: Quantum auxiliary data (15). There is no upper bound on its dimension, PDF p.4.
--   - `quantumTB`: TB marginal of (15), with X traced out, PDF p.4.
--   - `quantumTC`: TC marginal of (15), PDF p.4.
--   - `quantumPrivateInfo`: I(X;B|T) of (15); conditional independence given classical X eliminates H(T|X).
--   - `quantumOuterRegion`: Quantum-auxiliary outer region, PDF pp.4,7. The optional sum inequality is §II-C.
--   - `degradedClassicalRegion`: Reduced two-inequality classical region in Theorem 2, PDF p.4.
--   - `wordType`: Empirical type of a positive-length word; n=0 is never used by the theorem, PDF p.4.
--   - `CommonCode`: Common-message code, with an indexed word family (not assumed injective), PDF p.4.
--   - `CommonCode.Good`: Constant composition, l1 type approximation and joint maximum-error test, PDF p.4.
--   - `BroadcastInstrument`: Rectangular instrument with finitely many Kraus operators per classical branch, §I-B p.3 and §§III,V pp.7,12–13. Padding permits a common Kraus rank.
--   - `BroadcastInstrument.branch`: The subnormalized quantum state in a branch, PDF p.3.
--   - `BroadcastInstrument.output`: An instrument's explicit classical block output, not a coherent branch label, PDF p.3.
--   - `measurement`: A POVM as a classical-output channel, §I-B p.3.
--   - `CQCode`: CQ entanglement generation code, §III p.7: pure preparation for every common message, Bob's instrument, and Charlie's measurement. No shared resources/messages.
--   - `CQCode.decoded`: Decoding AFTER the channel, preserving Alice's reference, §III p.7.
--   - `commonEprTarget`: Both correct common labels AND an EPR of rank k in one joint target, p.7.
--   - `CQCode.Good`: Single JOINT fidelity test for every message, §III p.7.
--   - `cqAchievable`: Vanishing-error cq rates, §III p.7; first coordinate common bits, second EPR ebits.
--   - `cqGenerationCapacity`: CQ(N), the independently defined closed operational region, §III p.7.
--   - `ensembleBob`: Conditional reference/Bob state computed from the input and channel, p.8.
--   - `ensembleCharlie`: Conditional Charlie output of the same input, p.8.
--   - `ensembleCoherent`: I(A coherent-to BT), averaged over classical T. Individual terms may be negative, pp.7–8.
--   - `ensembleCommon`: Minimum of BOTH receiver Holevo informations, pp.7–8.
--   - `quantumCap`: Auxiliary cardinality cap in Theorems 3/5, PDF pp.8,11,14.
--   - `quantumInformationRegion`: Single-letter information union. `bounded=true` imposes the source's cap; otherwise every finite T is allowed. First coordinate is common classical or GHZ.
--   - `regularizedQuantumRegion`: RAW regularized union over strictly positive blocklengths, as defined p.4. The closures in the capacity theorems are separate, justified by pp.10,12.
--   - `rankGhzDensity`: Arbitrary-rank tripartite GHZ density, §IV p.11. m is positive when used as a target.
--   - `qqTarget`: PRODUCT EPR_k and GHZ_m, regrouped as Alice,Bob,Charlie, §IV p.11.
--   - `QQCode`: EPR–GHZ generation code: one pure encoding and separate CPTP decoders, p.11.
--   - `QQCode.decoded`: Correct composition order: channel first, local decoders second, pp.11–12. This corrects the ill-typed printed display in the operational definition on p.11.
--   - `QQCode.Good`: One joint fidelity test to the PRODUCT target; not two marginal tests, p.11.
--   - `qqAchievable`: Quantum rate order (GHZ,EPR_B), §IV p.11.
--   - `qqCapacity`: Q(N), the closed operational EPR–GHZ region, §IV p.11.
--   - `DephasingData`: Generalized-dephasing environment vectors need not be orthogonal, pp.3,8,11.
--   - `DephasingData.isometry`: U|x> = |x>_B |psi_x>_O, a rectangular isometry because the vectors are unit, pp.8,11.
--   - `generalizedDephasingBroadcast`: Keep B,C and discard ONLY E. N itself need not be isometric, Theorem 4 p.8.
--   - `dephasingRegion`: The dephasing entropy union, pp.8,11. F retains Charlie's part of O=CE (or all O=C). H(TX)-H(TO)=H(X|T)-H(O|T); no division by zero-weight p(t).
--   - `qutritPinching`: The rank-(2,1) qutrit pinching map, PDF p.8.
--   - `pinchingRegion`: Equation (25) p.8: downward closure of (f(p),p), 0≤p≤1. The printed Figure 1 interchanges the flat/curved resource roles and is not used.
--   - `twoEprTarget`: Two independent EPR resources regrouped by owner, §V p.13.
--   - `TwoEprCode`: Unassisted two-EPR GENERATION code: freely prepared pure block input with retained local references; separate decoders and no classical side messages, p.13.
--   - `TwoEprCode.decoded`: Unassisted generation output, with both external Alice registers retained, p.13.
--   - `twoEprAchievable`: Vanishing joint error to independent EPRs, §V p.13.
--   - `twoEprCapacity`: Closed two-EPR generation region; rank-one axes remain present, p.13.
--   - `TwoEprTransmissionCode`: Two-EPR TRANSMISSION code: Alice acts ONLY on supplied sender halves. The two external references are fixed independent EPR halves, not freely prepared, p.13.
--   - `TwoEprTransmissionCode.decoded`: External references untouched throughout encoding, channel and decoding, p.13.
--   - `twoEprTransmissionAchievable`: Independent entanglement transmission rates with no side communication, p.13.
--   - `twoEprTransmissionCapacity`: Closed transmission region, separately defined from generation, p.13.
--   - `twoEprInformation`: The two coherent informations of ONE joint input (references may be correlated), p.13.
--   - `assistedTarget`: AC and BC EPRs, product and regrouped as Alice,(Bob,(Charlie_AC,Charlie_BC)), p.13.
--   - `ReceiverMergingCode`: One-way receiver-assisted code, §V pp.12–13: Alice prepares a pure input; Bob retains an EPR half and sends ONE classical branch to Charlie, who decodes conditionally. No initial entanglement or other messages/shared randomness.
--   - `ReceiverMergingCode.decoded`: Sum over the ACTUAL communicated branch, retain both EPR resources, p.13.
--   - `assistedAchievable`: Simultaneous AC,BC rates from one-way Bob-to-Charlie assisted codes, p.13.
--   - `mergingInformation`: (I(A coherent-to BC),I(B coherent-to C)) from one pure reference/input, p.13.
--   - `rawRegularizedSuperposition`: Positive blocklength raw superposition union of §II p.4, keeping all three inequalities on the ACTUAL block channel; independent of the capacity region.
--   - `binaryExample`: The p.4 separation example: constant singleton Bob, noiseless binary Charlie.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, https://arxiv.org/abs/quant-ph/0603098v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-!
Quantum broadcast channels, arXiv:quant-ph/0603098v2.
All page references are PDF pages. Entropies/rates are in bits, distances are full
trace norms, and fidelity is squared. Operational regions are defined independently
of information regions. Only accepted pinned modules are imported. Compilation is
pending the batch handoff. Source corrections are recorded in MODERATION_NOTES.md.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Gap48.P39

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)
open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks holevoInfo)
open QAlgorithms.Papers.Independent.Dependency50.P19 (both epr mutualInformation marginalRA marginalRB)
open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)
open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity conditionalEntropy groupedChannelPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C X T E : Type}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]
variable [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- Classical-input broadcast channel, PDF p.2. Normalization excludes empty outputs. -/
structure CQChannel (X B C : Type) [Fintype B] [Fintype C] where
  state : X → Op (B × C)
  density : ∀ x, IsDensityMatrix (state x)

/-- The actual memoryless product output for an input word, PDF p.4. -/
def CQChannel.word {n : ℕ} (W : CQChannel X B C) (x : Fin n → X) :
    Op ((Fin n → B) × (Fin n → C)) :=
  fun i j => ∏ k, W.state (x k) (i.1 k, i.2 k) (j.1 k, j.2 k)

/-- Source rank convention floor(2^(nR)), PDF p.4; at nonnegative rates it is positive. -/
def rank (n : ℕ) (R : ℝ) : ℕ := ⌊Real.rpow 2 ((n : ℝ) * R)⌋₊

/-- Nonnegative classical common/Bob/Charlie rates, PDF p.4. -/
def NonnegativeTriple (r : ℝ × ℝ × ℝ) : Prop :=
  0 ≤ r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2

/-- Nonnegative two-resource rates, with task-specific coordinate interpretation. -/
def NonnegativePair (r : ℝ × ℝ) : Prop := 0 ≤ r.1 ∧ 0 ≤ r.2

/-- Deterministic words and separate decoding POVMs, PDF p.4. -/
structure CQBroadcastCode (X B C : Type) [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (n m k l : ℕ) where
  word : Fin m → Fin k → Fin l → (Fin n → X)
  bob : (Fin m × Fin k) → Op (Fin n → B)
  bob_povm : IsPOVM bob
  charlie : (Fin m × Fin l) → Op (Fin n → C)
  charlie_povm : IsPOVM charlie

/-- Joint maximum-error test, for EVERY message triple, PDF p.4. -/
def CQBroadcastCode.Good {n m k l : ℕ} (D : CQBroadcastCode X B C n m k l)
    (W : CQChannel X B C) (epsilon : ℝ) : Prop :=
  ∀ s i j, 1 - epsilon ≤ effectProb
    (Matrix.kronecker (D.bob (s, i)) (D.charlie (s, j))) (W.word (D.word s i j))

/-- Vanishing maximum joint error at fixed rates; all sufficiently large positive n, PDF p.4. -/
def cqBroadcastAchievable (W : CQChannel X B C) (r : ℝ × ℝ × ℝ) : Prop :=
  NonnegativeTriple r ∧ ∀ epsilon > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
    ∃ D : CQBroadcastCode X B C n (rank n r.1) (rank n r.2.1) (rank n r.2.2),
      D.Good W epsilon

/-- Operational CLOSED classical capacity, not an entropic definition, PDF p.4. -/
def cqBroadcastCapacity (W : CQChannel X B C) : Set (ℝ × ℝ × ℝ) :=
  closure {r | cqBroadcastAchievable W r}

/-- H(T) for a joint probability distribution, PDF pp.3–5. -/
def labelEntropy (p : Distribution (T × X)) : ℝ :=
  vnEntropy (Matrix.diagonal fun t => ((∑ x, p.val (t, x) : ℝ) : ℂ))

/-- The actual TB marginal of (14); weights stay subnormalized, including zero weights. -/
def cqTB (W : CQChannel X B C) (p : Distribution (T × X)) : Op (T × B) :=
  cqBlocks fun t => ∑ x, (p.val (t, x) : ℂ) • traceRight (W.state x)

/-- The actual TC marginal of (14), PDF p.4. -/
def cqTC (W : CQChannel X B C) (p : Distribution (T × X)) : Op (T × C) :=
  cqBlocks fun t => ∑ x, (p.val (t, x) : ℂ) • traceLeft (W.state x)

/-- I(X;B|T) in (14), using H(BT)-H(T)-sum p(t,x) H(B_x), PDF pp.4–5. -/
def superpositionPrivateInfo (W : CQChannel X B C) (p : Distribution (T × X)) : ℝ :=
  vnEntropy (cqTB W p) - labelEntropy p -
    ∑ t, ∑ x, p.val (t, x) * vnEntropy (traceRight (W.state x))

/-- I(T;C) in (14), PDF p.4. -/
def commonInfo (W : CQChannel X B C) (p : Distribution (T × X)) : ℝ :=
  mutualInformation (cqTC W p)

/-- I(X;B) in (14), PDF p.4. -/
def totalInfo (W : CQChannel X B C) (p : Distribution (T × X)) : ℝ :=
  holevoInfo (fun x => ∑ t, p.val (t, x)) (fun x => traceRight (W.state x))

/-- The three simultaneous inequalities (13), without hiding the sum-rate bound. -/
def SuperpositionBounds (W : CQChannel X B C) (p : Distribution (T × X))
    (r : ℝ × ℝ × ℝ) : Prop :=
  NonnegativeTriple r ∧ r.2.1 ≤ superpositionPrivateInfo W p ∧
    r.1 + r.2.2 ≤ commonInfo W p ∧ r.1 + r.2.1 + r.2.2 ≤ totalInfo W p

/-- Classical auxiliary cap, PDF pp.4,14; all physical output dimensions are positive. -/
def superpositionCap (X B C : Type) [Fintype X] [Fintype B] [Fintype C] : ℕ :=
  min (Fintype.card X) (Fintype.card B ^ 2 + Fintype.card C ^ 2 - 1)

/-- Classical auxiliary union; `none` allows every finite auxiliary, PDF p.4. -/
def superpositionRegion (W : CQChannel X B C) (cap : Option ℕ) : Set (ℝ × ℝ × ℝ) :=
  {r | ∃ t : ℕ, 0 < t ∧ (∀ b ∈ cap, t ≤ b) ∧
    ∃ p : Distribution (Fin t × X), SuperpositionBounds W p r}

/-- Source degradedness involves marginal channels, not a recovery map for BC, PDF pp.2,4. -/
def Degraded (W : CQChannel X B C) : Prop :=
  ∃ M : Superop B C, IsChannel M ∧ ∀ x, traceLeft (W.state x) = M (traceRight (W.state x))

/-- Bob marginal commutation only, PDF p.4. -/
def CommutingBob (W : CQChannel X B C) : Prop :=
  ∀ x y, traceRight (W.state x) * traceRight (W.state y) =
    traceRight (W.state y) * traceRight (W.state x)

/-- Quantum auxiliary data (15). There is no upper bound on its dimension, PDF p.4. -/
structure QuantumAux (X T : Type) [Fintype X] [Fintype T] where
  probability : Distribution X
  state : X → Op T
  density : ∀ x, IsDensityMatrix (state x)

/-- TB marginal of (15), with X traced out, PDF p.4. -/
def quantumTB (W : CQChannel X B C) (S : QuantumAux X T) : Op (T × B) :=
  ∑ x, (S.probability.val x : ℂ) • Matrix.kronecker (S.state x) (traceRight (W.state x))

/-- TC marginal of (15), PDF p.4. -/
def quantumTC (W : CQChannel X B C) (S : QuantumAux X T) : Op (T × C) :=
  ∑ x, (S.probability.val x : ℂ) • Matrix.kronecker (S.state x) (traceLeft (W.state x))

/-- I(X;B|T) of (15); conditional independence given classical X eliminates H(T|X). -/
def quantumPrivateInfo (W : CQChannel X B C) (S : QuantumAux X T) : ℝ :=
  vnEntropy (quantumTB W S) - vnEntropy (∑ x, (S.probability.val x : ℂ) • S.state x) -
    ∑ x, S.probability.val x * vnEntropy (traceRight (W.state x))

/-- Quantum-auxiliary outer region, PDF pp.4,7. The optional sum inequality is §II-C. -/
def quantumOuterRegion (W : CQChannel X B C) (sumBound : Bool) : Set (ℝ × ℝ × ℝ) :=
  {r | NonnegativeTriple r ∧ ∃ t : ℕ, 0 < t ∧ ∃ S : QuantumAux X (Fin t),
    r.2.1 ≤ quantumPrivateInfo W S ∧ r.1 + r.2.2 ≤ mutualInformation (quantumTC W S) ∧
    (sumBound = true → r.1 + r.2.1 + r.2.2 ≤
      holevoInfo S.probability.val (fun x => traceRight (W.state x)))}

/-- Reduced two-inequality classical region in Theorem 2, PDF p.4. -/
def degradedClassicalRegion (W : CQChannel X B C) : Set (ℝ × ℝ × ℝ) :=
  {r | NonnegativeTriple r ∧ ∃ t : ℕ, 0 < t ∧ t ≤ min (Fintype.card X) (Fintype.card B ^ 2) ∧
    ∃ p : Distribution (Fin t × X), r.2.1 ≤ superpositionPrivateInfo W p ∧ r.1 + r.2.2 ≤ commonInfo W p}

/-- Empirical type of a positive-length word; n=0 is never used by the theorem, PDF p.4. -/
def wordType {n : ℕ} (x : Fin n → X) (a : X) : ℝ :=
  ((Finset.univ.filter fun i => x i = a).card : ℝ) / n

/-- Common-message code, with an indexed word family (not assumed injective), PDF p.4. -/
structure CommonCode (X B C : Type) [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (n m : ℕ) where
  word : Fin m → (Fin n → X)
  bob : Fin m → Op (Fin n → B)
  bob_povm : IsPOVM bob
  charlie : Fin m → Op (Fin n → C)
  charlie_povm : IsPOVM charlie

/-- Constant composition, l1 type approximation and joint maximum-error test, PDF p.4. -/
def CommonCode.Good {n m : ℕ} (D : CommonCode X B C n m) (W : CQChannel X B C)
    (p : Distribution X) (epsilon delta : ℝ) : Prop :=
  ∃ P : X → ℝ, (∑ x, |P x - p.val x|) ≤ delta ∧
    ∀ s, (∀ x, wordType (D.word s) x = P x) ∧
      1 - epsilon ≤ effectProb (Matrix.kronecker (D.bob s) (D.charlie s)) (W.word (D.word s))

/-- Normalization sanity: no asymptotic definition uses the empty block. -/
example : rank 0 0 = 1 := by simp [rank]

/-- The zero-use product is the singleton identity. -/
example (W : CQChannel X B C) (x : Fin 0 → X)
    (i j : (Fin 0 → B) × (Fin 0 → C)) : W.word x i j = 1 := by simp [CQChannel.word]

/-- Empirical type on one use is the point mass at the input symbol. -/
example (x : Fin 1 → X) (a : X) : wordType x a = (if x 0 = a then 1 else 0) := by
  by_cases h : x 0 = a
  · have hfilter :
        (Finset.univ.filter fun i : Fin 1 => x i = a) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      rw [hi]
      exact h
    unfold wordType
    rw [hfilter]
    simp [h]
  · simp [wordType, h]

/-- Rectangular instrument with finitely many Kraus operators per classical branch,
§I-B p.3 and §§III,V pp.7,12–13. Padding permits a common Kraus rank. -/
structure BroadcastInstrument (I J O : Type) [Fintype I] [Fintype J] [Fintype O] [DecidableEq I] where
  krausRank : ℕ
  kraus : O → Fin krausRank → Matrix J I ℂ
  normalized : ∑ o, ∑ k, (kraus o k)ᴴ * kraus o k = 1

/-- The subnormalized quantum state in a branch, PDF p.3. -/
def BroadcastInstrument.branch {I J O : Type} [Fintype I] [Fintype J] [Fintype O] [DecidableEq I]
    (D : BroadcastInstrument I J O) (o : O) : Superop I J := krausApply (D.kraus o)

/-- An instrument's explicit classical block output, not a coherent branch label, PDF p.3. -/
def BroadcastInstrument.output {I J O : Type} [Fintype I] [Fintype J] [Fintype O] [DecidableEq I]
    (D : BroadcastInstrument I J O) : Superop I (O × J) :=
  fun rho => cqBlocks fun o => D.branch o rho

/-- A POVM as a classical-output channel, §I-B p.3. -/
def measurement {I O : Type} [Fintype I] [DecidableEq O] (M : O → Op I) : Superop I O :=
  fun rho => Matrix.diagonal fun o => (M o * rho).trace

/-- CQ entanglement generation code, §III p.7: pure preparation for every common
message, Bob's instrument, and Charlie's measurement. No shared resources/messages. -/
structure CQCode (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (n m k : ℕ) where
  encode : Fin m → EuclideanSpace ℂ (Fin k × (Fin n → A))
  unit : ∀ s, IsState (encode s)
  bob : BroadcastInstrument (Fin n → B) (Fin k) (Fin m)
  charlie : Fin m → Op (Fin n → C)
  charlie_povm : IsPOVM charlie

/-- Decoding AFTER the channel, preserving Alice's reference, §III p.7. -/
def CQCode.decoded {n m k : ℕ} (D : CQCode A B C n m k)
    (N : Superop A (B × C)) (s : Fin m) : Op (Fin k × ((Fin m × Fin k) × Fin m)) :=
  idTensorSuperop (both D.bob.output (measurement D.charlie))
    (idTensorSuperop (groupedChannelPower N n) (pureDensity (D.encode s)))

/-- Both correct common labels AND an EPR of rank k in one joint target, p.7. -/
def commonEprTarget (m k : ℕ) (s : Fin m) : Op (Fin k × ((Fin m × Fin k) × Fin m)) :=
  fun i j => if i.2.1.1 = s ∧ i.2.2 = s ∧ j.2.1.1 = s ∧ j.2.2 = s then
    epr k (i.1, i.2.1.2) (j.1, j.2.1.2) else 0

/-- Single JOINT fidelity test for every message, §III p.7. -/
def CQCode.Good {n m k : ℕ} (D : CQCode A B C n m k) (N : Superop A (B × C))
    (epsilon : ℝ) : Prop :=
  ∀ s, 1 - epsilon ≤ squaredFidelity (D.decoded N s) (commonEprTarget m k s)

/-- Vanishing-error cq rates, §III p.7; first coordinate common bits, second EPR ebits. -/
def cqAchievable (N : Superop A (B × C)) (r : ℝ × ℝ) : Prop :=
  NonnegativePair r ∧ ∀ epsilon > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
    ∃ D : CQCode A B C n (rank n r.1) (rank n r.2), D.Good N epsilon

/-- CQ(N), the independently defined closed operational region, §III p.7. -/
def cqGenerationCapacity (N : Superop A (B × C)) : Set (ℝ × ℝ) := closure {r | cqAchievable N r}

/-- Conditional reference/Bob state computed from the input and channel, p.8. -/
def ensembleBob {a : ℕ} (S : PureEnsemble (Fin a × A)) (N : Superop A (B × C))
    (s : Fin S.count) : Op (Fin a × B) :=
  marginalRA (idTensorSuperop N (pureDensity (S.vector s)))

/-- Conditional Charlie output of the same input, p.8. -/
def ensembleCharlie {a : ℕ} (S : PureEnsemble (Fin a × A)) (N : Superop A (B × C))
    (s : Fin S.count) : Op C := traceLeft (traceLeft (idTensorSuperop N (pureDensity (S.vector s))))

/-- I(A coherent-to BT), averaged over classical T. Individual terms may be negative, pp.7–8. -/
def ensembleCoherent {a : ℕ} (S : PureEnsemble (Fin a × A)) (N : Superop A (B × C)) : ℝ :=
  ∑ s, S.weight s * (vnEntropy (traceLeft (ensembleBob S N s)) - vnEntropy (ensembleBob S N s))

/-- Minimum of BOTH receiver Holevo informations, pp.7–8. -/
def ensembleCommon {a : ℕ} (S : PureEnsemble (Fin a × A)) (N : Superop A (B × C)) : ℝ :=
  min (holevoInfo S.weight (fun s => traceLeft (ensembleBob S N s)))
    (holevoInfo S.weight (ensembleCharlie S N))

/-- Auxiliary cardinality cap in Theorems 3/5, PDF pp.8,11,14. -/
def quantumCap (A B C : Type) [Fintype A] [Fintype B] [Fintype C] : ℕ :=
  min (Fintype.card A ^ 2) (Fintype.card B ^ 2 + Fintype.card C ^ 2 - 1)

/-- Single-letter information union. `bounded=true` imposes the source's cap;
otherwise every finite T is allowed. First coordinate is common classical or GHZ. -/
def quantumInformationRegion (N : Superop A (B × C)) (bounded : Bool) : Set (ℝ × ℝ) :=
  {r | NonnegativePair r ∧ ∃ a : ℕ, 0 < a ∧
    ∃ S : PureEnsemble (Fin a × A), 0 < S.count ∧
      (bounded = true → S.count ≤ quantumCap A B C) ∧
      r.2 ≤ ensembleCoherent S N ∧ r.1 ≤ ensembleCommon S N}

/-- RAW regularized union over strictly positive blocklengths, as defined p.4.
The closures in the capacity theorems are separate, justified by pp.10,12. -/
def regularizedQuantumRegion (N : Superop A (B × C)) : Set (ℝ × ℝ) :=
  {r | ∃ n : ℕ, 0 < n ∧ ((n : ℝ) * r.1, (n : ℝ) * r.2) ∈
    quantumInformationRegion (groupedChannelPower N n) true}

/-- Arbitrary-rank tripartite GHZ density, §IV p.11. m is positive when used as a target. -/
def rankGhzDensity (m : ℕ) : Op (Fin m × (Fin m × Fin m)) :=
  fun i j => if i.1 = i.2.1 ∧ i.1 = i.2.2 ∧ j.1 = j.2.1 ∧ j.1 = j.2.2 then
    (m : ℂ)⁻¹ else 0

/-- PRODUCT EPR_k and GHZ_m, regrouped as Alice,Bob,Charlie, §IV p.11. -/
def qqTarget (m k : ℕ) : Op ((Fin k × Fin m) × ((Fin k × Fin m) × Fin m)) :=
  fun i j => epr k (i.1.1, i.2.1.1) (j.1.1, j.2.1.1) *
    rankGhzDensity m (i.1.2, (i.2.1.2, i.2.2)) (j.1.2, (j.2.1.2, j.2.2))

/-- EPR–GHZ generation code: one pure encoding and separate CPTP decoders, p.11. -/
structure QQCode (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (n m k : ℕ) where
  encode : EuclideanSpace ℂ ((Fin k × Fin m) × (Fin n → A))
  unit : IsState encode
  bob : Superop (Fin n → B) (Fin k × Fin m)
  bob_channel : IsChannel bob
  charlie : Superop (Fin n → C) (Fin m)
  charlie_channel : IsChannel charlie

/-- Correct composition order: channel first, local decoders second, pp.11–12.
This corrects the ill-typed printed display in the operational definition on p.11. -/
def QQCode.decoded {n m k : ℕ} (D : QQCode A B C n m k) (N : Superop A (B × C)) :
    Op ((Fin k × Fin m) × ((Fin k × Fin m) × Fin m)) :=
  idTensorSuperop (both D.bob D.charlie)
    (idTensorSuperop (groupedChannelPower N n) (pureDensity D.encode))

/-- One joint fidelity test to the PRODUCT target; not two marginal tests, p.11. -/
def QQCode.Good {n m k : ℕ} (D : QQCode A B C n m k) (N : Superop A (B × C))
    (epsilon : ℝ) : Prop := 1 - epsilon ≤ squaredFidelity (D.decoded N) (qqTarget m k)

/-- Quantum rate order (GHZ,EPR_B), §IV p.11. -/
def qqAchievable (N : Superop A (B × C)) (r : ℝ × ℝ) : Prop :=
  NonnegativePair r ∧ ∀ epsilon > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
    ∃ D : QQCode A B C n (rank n r.1) (rank n r.2), D.Good N epsilon

/-- Q(N), the closed operational EPR–GHZ region, §IV p.11. -/
def qqCapacity (N : Superop A (B × C)) : Set (ℝ × ℝ) := closure {r | qqAchievable N r}

/-- Zero-rate resources have rank one, not dimension zero, pp.4,7,11. -/
example (n : ℕ) : rank n 0 = 1 := by simp [rank]

/-- Arbitrary-rank GHZ normalization formula has unit rank-one value. -/
example : rankGhzDensity 1 (0, (0, 0)) (0, (0, 0)) = 1 := by simp [rankGhzDensity]

/-- The independent target is constructed as the actual product, p.11. -/
example (m k : ℕ) (i j : (Fin k × Fin m) × ((Fin k × Fin m) × Fin m)) :
    qqTarget m k i j = epr k (i.1.1, i.2.1.1) (j.1.1, j.2.1.1) *
      rankGhzDensity m (i.1.2, (i.2.1.2, i.2.2)) (j.1.2, (j.2.1.2, j.2.2)) := rfl

/-- A common label appears as a diagonal block, so no unintended coherence is encoded. -/
example {I J O : Type} [Fintype I] [Fintype J] [Fintype O] [DecidableEq I]
    (D : BroadcastInstrument I J O) (rho : Op I) (o p : O) (h : o ≠ p) (i j : J) :
    D.output rho (o, i) (p, j) = 0 := by simp [BroadcastInstrument.output, cqBlocks, h]

/-- Generalized-dephasing environment vectors need not be orthogonal, pp.3,8,11. -/
structure DephasingData (X O : Type) [Fintype O] where
  state : X → EuclideanSpace ℂ O
  unit : ∀ x, IsState (state x)

/-- U|x> = |x>_B |psi_x>_O, a rectangular isometry because the vectors are unit, pp.8,11. -/
def DephasingData.isometry {O : Type} [Fintype O] (D : DephasingData X O) :
    Matrix (X × O) X ℂ := fun i x => if i.1 = x then D.state x i.2 else 0

/-- Keep B,C and discard ONLY E. N itself need not be isometric, Theorem 4 p.8. -/
def generalizedDephasingBroadcast (D : DephasingData X (C × E)) : Superop X (X × C) :=
  fun rho => idTensorSuperop traceRight (conjSuperop D.isometry rho)

/-- The dephasing entropy union, pp.8,11. F retains Charlie's part of O=CE
(or all O=C). H(TX)-H(TO)=H(X|T)-H(O|T); no division by zero-weight p(t). -/
def dephasingRegion {O : Type} [Fintype O] [DecidableEq O]
    (D : DephasingData X O) (F : Superop O C) : Set (ℝ × ℝ) :=
  {r | NonnegativePair r ∧ ∃ t : ℕ, 0 < t ∧ t ≤ Fintype.card X ∧
    ∃ p : Distribution (Fin t × X),
      r.2 ≤ vnEntropy (Matrix.diagonal fun tx => (p.val tx : ℂ)) -
        vnEntropy (cqBlocks fun s => ∑ x, (p.val (s, x) : ℂ) • pureDensity (D.state x)) ∧
      r.1 ≤ mutualInformation (cqBlocks fun s =>
        ∑ x, (p.val (s, x) : ℂ) • F (pureDensity (D.state x)))}

/-- The rank-(2,1) qutrit pinching map, PDF p.8. -/
def qutritPinching : Superop (Fin 3) (Fin 3) :=
  fun rho i j => if (i.val < 2 ↔ j.val < 2) then rho i j else 0

/-- Equation (25) p.8: downward closure of (f(p),p), 0≤p≤1.
The printed Figure 1 interchanges the flat/curved resource roles and is not used. -/
def pinchingRegion : Set (ℝ × ℝ) :=
  {r | NonnegativePair r ∧ ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ r.2 ≤ p ∧
    r.1 ≤ if p ≤ 1 / 2 then 1 else binEntropy2 p}

/-- The pinching retains 01 coherence. -/
example (rho : Op (Fin 3)) : qutritPinching rho 0 1 = rho 0 1 := by simp [qutritPinching]

/-- The pinching deletes 02 coherence. -/
example (rho : Op (Fin 3)) : qutritPinching rho 0 2 = 0 := by simp [qutritPinching]

/-- The equation (25) breakpoint is (common/GHZ,EPR)=(1,1/2). -/
example : (1, (1 / 2 : ℝ)) ∈ pinchingRegion := by
  refine ⟨⟨by norm_num, by norm_num⟩, 1 / 2, by norm_num, by norm_num, le_rfl, ?_⟩
  norm_num

/-- The dilation's Bob label is the actual input basis label. -/
example {O : Type} [Fintype O] (D : DephasingData X O) (x : X) (o : O) :
    D.isometry (x, o) x = D.state x o := by simp [DephasingData.isometry]

/-- Two independent EPR resources regrouped by owner, §V p.13. -/
def twoEprTarget (k l : ℕ) : Op ((Fin k × Fin l) × (Fin k × Fin l)) :=
  fun i j => epr k (i.1.1, i.2.1) (j.1.1, j.2.1) *
    epr l (i.1.2, i.2.2) (j.1.2, j.2.2)

/-- Unassisted two-EPR GENERATION code: freely prepared pure block input with
retained local references; separate decoders and no classical side messages, p.13. -/
structure TwoEprCode (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (n k l : ℕ) where
  encode : EuclideanSpace ℂ ((Fin k × Fin l) × (Fin n → A))
  unit : IsState encode
  bob : Superop (Fin n → B) (Fin k)
  bob_channel : IsChannel bob
  charlie : Superop (Fin n → C) (Fin l)
  charlie_channel : IsChannel charlie

/-- Unassisted generation output, with both external Alice registers retained, p.13. -/
def TwoEprCode.decoded {n k l : ℕ} (D : TwoEprCode A B C n k l) (N : Superop A (B × C)) :
    Op ((Fin k × Fin l) × (Fin k × Fin l)) :=
  idTensorSuperop (both D.bob D.charlie)
    (idTensorSuperop (groupedChannelPower N n) (pureDensity D.encode))

/-- Vanishing joint error to independent EPRs, §V p.13. -/
def twoEprAchievable (N : Superop A (B × C)) (r : ℝ × ℝ) : Prop :=
  NonnegativePair r ∧ ∀ epsilon > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
    ∃ D : TwoEprCode A B C n (rank n r.1) (rank n r.2),
      1 - epsilon ≤ squaredFidelity (D.decoded N) (twoEprTarget (rank n r.1) (rank n r.2))

/-- Closed two-EPR generation region; rank-one axes remain present, p.13. -/
def twoEprCapacity (N : Superop A (B × C)) : Set (ℝ × ℝ) := closure {r | twoEprAchievable N r}

/-- Two-EPR TRANSMISSION code: Alice acts ONLY on supplied sender halves.
The two external references are fixed independent EPR halves, not freely prepared, p.13. -/
structure TwoEprTransmissionCode (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (n k l : ℕ) where
  encode : Superop (Fin k × Fin l) (Fin n → A)
  encode_channel : IsChannel encode
  bob : Superop (Fin n → B) (Fin k)
  bob_channel : IsChannel bob
  charlie : Superop (Fin n → C) (Fin l)
  charlie_channel : IsChannel charlie

/-- External references untouched throughout encoding, channel and decoding, p.13. -/
def TwoEprTransmissionCode.decoded {n k l : ℕ} (D : TwoEprTransmissionCode A B C n k l)
    (N : Superop A (B × C)) : Op ((Fin k × Fin l) × (Fin k × Fin l)) :=
  idTensorSuperop (both D.bob D.charlie ∘ groupedChannelPower N n ∘ D.encode) (twoEprTarget k l)

/-- Independent entanglement transmission rates with no side communication, p.13. -/
def twoEprTransmissionAchievable (N : Superop A (B × C)) (r : ℝ × ℝ) : Prop :=
  NonnegativePair r ∧ ∀ epsilon > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
    ∃ D : TwoEprTransmissionCode A B C n (rank n r.1) (rank n r.2),
      1 - epsilon ≤ squaredFidelity (D.decoded N) (twoEprTarget (rank n r.1) (rank n r.2))

/-- Closed transmission region, separately defined from generation, p.13. -/
def twoEprTransmissionCapacity (N : Superop A (B × C)) : Set (ℝ × ℝ) :=
  closure {r | twoEprTransmissionAchievable N r}

/-- The two coherent informations of ONE joint input (references may be correlated), p.13. -/
def twoEprInformation {AB AC : Type} [Fintype AB] [Fintype AC]
    [DecidableEq AB] [DecidableEq AC] (N : Superop A (B × C))
    (psi : EuclideanSpace ℂ ((AB × AC) × A)) : ℝ × ℝ :=
  let rho := idTensorSuperop N (pureDensity psi)
  let rhoAB_B : Op (AB × B) := fun i j => ∑ ac, ∑ c, rho ((i.1, ac), (i.2, c)) ((j.1, ac), (j.2, c))
  let rhoAC_C : Op (AC × C) := fun i j => ∑ ab, ∑ b, rho ((ab, i.1), (b, i.2)) ((ab, j.1), (b, j.2))
  (vnEntropy (traceLeft rhoAB_B) - vnEntropy rhoAB_B,
    vnEntropy (traceLeft rhoAC_C) - vnEntropy rhoAC_C)

/-- The independent EPR target is product, not an arbitrary correlated pair. -/
example (k l : ℕ) (i j : (Fin k × Fin l) × (Fin k × Fin l)) :
    twoEprTarget k l i j = epr k (i.1.1, i.2.1) (j.1.1, j.2.1) *
      epr l (i.1.2, i.2.2) (j.1.2, j.2.2) := rfl

/-- With both resources trivial the target is a normalized singleton state. -/
example : twoEprTarget 1 1 ((0, 0), (0, 0)) ((0, 0), (0, 0)) = 1 := by
  simp [twoEprTarget, epr]

/-- AC and BC EPRs, product and regrouped as Alice,(Bob,(Charlie_AC,Charlie_BC)), p.13. -/
def assistedTarget (k l : ℕ) : Op (Fin k × (Fin l × (Fin k × Fin l))) :=
  fun i j => epr k (i.1, i.2.2.1) (j.1, j.2.2.1) *
    epr l (i.2.1, i.2.2.2) (j.2.1, j.2.2.2)

/-- One-way receiver-assisted code, §V pp.12–13: Alice prepares a pure input;
Bob retains an EPR half and sends ONE classical branch to Charlie, who decodes
conditionally. No initial entanglement or other messages/shared randomness. -/
structure ReceiverMergingCode (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (n k l m : ℕ) where
  encode : EuclideanSpace ℂ (Fin k × (Fin n → A))
  unit : IsState encode
  bob : BroadcastInstrument (Fin n → B) (Fin l) (Fin m)
  charlie : Fin m → Superop (Fin n → C) (Fin k × Fin l)
  charlie_channel : ∀ s, IsChannel (charlie s)

/-- Sum over the ACTUAL communicated branch, retain both EPR resources, p.13. -/
def ReceiverMergingCode.decoded {n k l m : ℕ} (D : ReceiverMergingCode A B C n k l m)
    (N : Superop A (B × C)) : Op (Fin k × (Fin l × (Fin k × Fin l))) :=
  ∑ s, idTensorSuperop (both (D.bob.branch s) (D.charlie s))
    (idTensorSuperop (groupedChannelPower N n) (pureDensity D.encode))

/-- Simultaneous AC,BC rates from one-way Bob-to-Charlie assisted codes, p.13. -/
def assistedAchievable (N : Superop A (B × C)) (r : ℝ × ℝ) : Prop :=
  NonnegativePair r ∧ ∀ epsilon > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
    ∃ m : ℕ, 0 < m ∧ ∃ D : ReceiverMergingCode A B C n (rank n r.1) (rank n r.2) m,
      1 - epsilon ≤ squaredFidelity (D.decoded N) (assistedTarget (rank n r.1) (rank n r.2))

/-- (I(A coherent-to BC),I(B coherent-to C)) from one pure reference/input, p.13. -/
def mergingInformation {R : Type} [Fintype R] [DecidableEq R]
    (N : Superop A (B × C)) (psi : EuclideanSpace ℂ (R × A)) : ℝ × ℝ :=
  let rho := idTensorSuperop N (pureDensity psi)
  let bc := traceLeft rho
  (vnEntropy bc - vnEntropy rho, vnEntropy (traceLeft bc) - vnEntropy bc)

/-- Positive blocklength raw superposition union of §II p.4, keeping all three
inequalities on the ACTUAL block channel; independent of the capacity region. -/
def rawRegularizedSuperposition (W : CQChannel X B C) : Set (ℝ × ℝ × ℝ) :=
  {r | NonnegativeTriple r ∧ ∃ n t : ℕ, 0 < n ∧ 0 < t ∧
    t ≤ superpositionCap (Fin n → X) (Fin n → B) (Fin n → C) ∧
    ∃ p : Distribution (Fin t × (Fin n → X)),
      let tb := cqBlocks fun s => ∑ x, (p.val (s, x) : ℂ) • traceRight (W.word x)
      let tc := cqBlocks fun s => ∑ x, (p.val (s, x) : ℂ) • traceLeft (W.word x)
      (n : ℝ) * r.2.1 ≤ vnEntropy tb - labelEntropy p -
        ∑ s, ∑ x, p.val (s, x) * vnEntropy (traceRight (W.word x)) ∧
      (n : ℝ) * (r.1 + r.2.2) ≤ mutualInformation tc ∧
      (n : ℝ) * (r.1 + r.2.1 + r.2.2) ≤
        holevoInfo (fun x => ∑ s, p.val (s, x)) (fun x => traceRight (W.word x))}

/-- The p.4 separation example: constant singleton Bob, noiseless binary Charlie. -/
def binaryExample : CQChannel Bool Unit Bool where
  state x := pureDensity (ket (Unit.unit, x))
  density x := ⟨pureDensity_posSemidef _, by simp [pureDensity, ket, Matrix.trace]⟩

/-- Alice–Charlie and Bob–Charlie resources are independently tensorized. -/
example (k l : ℕ) (i j : Fin k × (Fin l × (Fin k × Fin l))) :
    assistedTarget k l i j = epr k (i.1, i.2.2.1) (j.1, j.2.2.1) *
      epr l (i.2.1, i.2.2.2) (j.2.1, j.2.2.2) := rfl

/-- Bob is constant and Charlie retains the binary basis value in the separation example. -/
example (x : Bool) : binaryExample.state x (Unit.unit, x) (Unit.unit, x) = 1 := by
  simp [binaryExample, pureDensity, ket]

end QAlgorithms.Papers.Independent.Gap48.P39


