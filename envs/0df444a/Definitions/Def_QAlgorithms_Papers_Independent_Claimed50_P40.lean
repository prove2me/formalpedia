-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40
-- name    : QAlgorithms_Papers_Independent_Claimed50_P40
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:45:37.320203+00:00
-- url     : https://prove2.me/theorems/e8a8dff3-b577-450c-b895-086e1e82a90d
-- title:
--   Definitions for The Capacity of the Quantum Multiple Access Channel
-- statement:
--   The objects the formalized statements of *The Capacity of the Quantum Multiple Access Channel* (arXiv:quant-ph/9807019) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `InBlocks`: PDF pp.1,3: membership in a direct sum of full matrix blocks.
--   - `InBlockPower`: PDF p.2: membership in the n-fold tensor power of that algebra.
--   - `ClassicalChannel`: PDF pp.1-2: a finite, nonempty, independent-sender classical-input channel.
--   - `Access`: PDF pp.1-3: a receiver's canonical algebra and its faithful unital *-embedding. The extension of `embed` off the block algebra is immaterial.
--   - `Network`: PDF p.1: receiver accesses commute elementwise; they may overlap centrally.
--   - `fullAccess`: PDF p.4, section VI: the sole receiver has the whole declared output algebra.
--   - `singleReceiver`: PDF p.4, section VI: there is exactly one receiver.
--   - `restrictedState`: PDF p.3: restriction of a state to a receiver, in its intrinsic-trace coordinates. Only in-block matrix units belong to the receiver algebra.
--   - `blockOutput`: PDF p.2: the memoryless n-use channel, a tensor product of single-use states.
--   - `MultiwayBlockCode`: PDF p.2: fixed deterministic encoders, arbitrary block POVMs, nonempty message sets. Encoding need not be injective. Receiver j's decoder acts in its n-copy algebra.
--   - `codeRate`: PDF p.2: bits per use. Codes carry the positive length and message-cardinality guards.
--   - `averageTupleError`: PDF p.2: probability of any incorrectly decoded sender message, uniformly averaged on the entire independent message tuple, separately for each receiver.
--   - `capacityRegion`: PDF p.2: nonnegative operational achievable rates, with codes for every sufficiently large positive length, and average error at every receiver.
--   - `IsConcatenation`: PDF p.2: actual concatenation, including a common pairing of messages at every receiver and tensor-product decoding on the two subblocks.
--   - `Letters`: PDF p.2: coordinates of the senders in a subset, including the empty subset.
--   - `InputLaw`: PDF pp.2-3: one independent a priori law for each sender; zeros are permitted.
--   - `senderMarginalWeight`: PDF p.2: product marginal probability on a subset of sender registers.
--   - `inputWeight`: PDF p.2: full independent input probability.
--   - `Matches`: PDF p.2: matching the retained classical registers when tracing out the rest.
--   - `classicalMarginal`: PDF pp.2-3: classical marginal of the channel state, computed from the input law.
--   - `channelMarginal`: PDF pp.2-3: the marginal gamma_{X(J)Y}, with every omitted input summed out.
--   - `classicalEntropy`: PDF p.3: H(X(J)), in bits, with intrinsic trace.
--   - `jointEntropy`: PDF p.3: H(Y X(J)), in bits, from the computed channel-state marginal.
--   - `conditionalOutputEntropy`: PDF p.3: H(Y|X(J)) = H(YX(J)) - H(X(J)).
--   - `conditionalInformation`: PDF p.3: conditional mutual information, defined by the four entropy terms, rather than assuming the independence identity asserted in the theorem.
--   - `senderOutputMutualInformation`: PDF pp.3,7: I(X(J) : Y X(K)); used only with disjoint J,K.
--   - `averagedChannel`: PDF p.2: P_J W averages precisely J; the remaining argument is J-complement.
--   - `averagedChannelEntropy`: PDF p.3: H(P_J W | P_{J-complement}), an average over the remaining inputs.
--   - `meanOutputEntropy`: PDF p.3: H(W|P_[s]), averaging entropy of the original channel outputs.
--   - `productLawRateRegion`: PDF pp.4,6: the fixed-product-law single-letter rate polytope. Every subset, including empty and full, is tested.
--   - `MixtureDominates`: PDF p.3, theorem 3: one mixture, chosen before both sender subset and receiver. All channel states use the SAME channel, with product laws conditional on the mixture label.
--   - `mixtureRegion`: PDF p.3: preclosure outer region; nonnegativity is not lost on convexification.
--   - `IsUpperExtreme`: PDF p.7: extreme point AND maximal for the coordinatewise order, in the fixed-law polytope. This excludes the origin when some positive rate is possible.
--   - `predecessors`: PDF p.7: a permutation's preceding classical registers; none precedes index zero.
--   - `permutationRates`: PDF p.7: permutation rate tuple, computed by the information formula on the page.
--   - `ludersBranch`: PDF p.4: the positive square-root (Luders) measurement branch.
--   - `tenderOperation`: PDF p.4, lemma 7: the actual nonselective square-root operation delta.
--   - `labelledOperation`: PDF p.4, lemma 7: Delta, retaining the actual classical measurement outcome.
--   - `idealLabel`: PDF p.4: the ideal classical label tensored with an undisturbed state.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, https://arxiv.org/abs/quant-ph/9807019v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-!
Statements from A. Winter, arXiv:quant-ph/9807019v3.
Finite C*-algebras are represented once, without representation multiplicities, as
block-diagonal matrix algebras. Ordinary matrix trace is therefore the intrinsic
trace (one on minimal projections). Receiver algebras are embedded unital
*-subalgebras, not prescribed tensor factors. All logarithms are in bits.
Quantum-input operational extensions in section VII are explicitly deferred.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1,3: membership in a direct sum of full matrix blocks. -/
def InBlocks {d : ℕ} (block : Fin d → ℕ) (T : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ a b, block a ≠ block b → T a b = 0

/-- PDF p.2: membership in the n-fold tensor power of that algebra. -/
def InBlockPower {d : ℕ} (block : Fin d → ℕ) (n : ℕ)
    (T : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop :=
  ∀ a b, (∃ k, block (a k) ≠ block (b k)) → T a b = 0

/-- PDF pp.1-2: a finite, nonempty, independent-sender classical-input channel. -/
structure ClassicalChannel (s : ℕ) where
  senders_pos : 0 < s
  alphabet : Fin s → ℕ
  alphabet_pos : ∀ i, 0 < alphabet i
  output : ℕ
  output_pos : 0 < output
  block : Fin output → ℕ
  state : (∀ i, Fin (alphabet i)) → Matrix (Fin output) (Fin output) ℂ
  normalized : ∀ x, IsDensityMatrix (state x)
  in_algebra : ∀ x, InBlocks block (state x)

/-- PDF pp.1-3: a receiver's canonical algebra and its faithful unital *-embedding.
The extension of `embed` off the block algebra is immaterial. -/
structure Access {s : ℕ} (C : ClassicalChannel s) where
  dim : ℕ
  dim_pos : 0 < dim
  block : Fin dim → ℕ
  embed : Matrix (Fin dim) (Fin dim) ℂ →ₗ[ℂ]
    Matrix (Fin C.output) (Fin C.output) ℂ
  unital : embed 1 = 1
  preserves_blocks : ∀ T, InBlocks block T → InBlocks C.block (embed T)
  preserves_star : ∀ T, InBlocks block T → embed Tᴴ = (embed T)ᴴ
  preserves_mul : ∀ T U, InBlocks block T → InBlocks block U →
    embed (T * U) = embed T * embed U
  faithful : ∀ T U, InBlocks block T → InBlocks block U → embed T = embed U → T = U

/-- PDF p.1: receiver accesses commute elementwise; they may overlap centrally. -/
structure Network {s : ℕ} (C : ClassicalChannel s) (r : ℕ) where
  receivers_pos : 0 < r
  access : Fin r → Access C
  commute : ∀ j k, j ≠ k → ∀ T U,
    InBlocks (access j).block T → InBlocks (access k).block U →
    (access j).embed T * (access k).embed U =
      (access k).embed U * (access j).embed T

/-- PDF p.4, section VI: the sole receiver has the whole declared output algebra. -/
def fullAccess {s : ℕ} (C : ClassicalChannel s) : Access C where
  dim := C.output
  dim_pos := C.output_pos
  block := C.block
  embed := LinearMap.id
  unital := rfl
  preserves_blocks := fun _ h => h
  preserves_star := fun _ _ => rfl
  preserves_mul := fun _ _ _ _ => rfl
  faithful := fun _ _ _ _ h => h

/-- PDF p.4, section VI: there is exactly one receiver. -/
def singleReceiver {s : ℕ} (C : ClassicalChannel s) : Network C 1 where
  receivers_pos := by omega
  access := fun _ => fullAccess C
  commute := by
    intro j k h
    exact (h (Subsingleton.elim j k)).elim

/-- PDF p.3: restriction of a state to a receiver, in its intrinsic-trace coordinates.
Only in-block matrix units belong to the receiver algebra. -/
def restrictedState {s : ℕ} {C : ClassicalChannel s} (A : Access C)
    (rho : Matrix (Fin C.output) (Fin C.output) ℂ) :
    Matrix (Fin A.dim) (Fin A.dim) ℂ :=
  fun a b => if A.block a = A.block b then
    (rho * A.embed (Matrix.single b a 1)).trace else 0

/-- PDF p.2: the memoryless n-use channel, a tensor product of single-use states. -/
def blockOutput {s : ℕ} (C : ClassicalChannel s) (n : ℕ)
    (word : ∀ i, Fin n → Fin (C.alphabet i)) :
    Matrix (Fin n → Fin C.output) (Fin n → Fin C.output) ℂ :=
  fun a b => ∏ k, C.state (fun i => word i k) (a k) (b k)

/-- PDF p.2: fixed deterministic encoders, arbitrary block POVMs, nonempty message sets.
Encoding need not be injective. Receiver j's decoder acts in its n-copy algebra. -/
structure MultiwayBlockCode {s r : ℕ} {C : ClassicalChannel s} (N : Network C r) (n : ℕ) where
  length_pos : 0 < n
  messages : Fin s → ℕ
  messages_pos : ∀ i, 0 < messages i
  encode : ∀ i, Fin (messages i) → Fin n → Fin (C.alphabet i)
  decode : ∀ j : Fin r, (∀ i, Fin (messages i)) →
    Matrix (Fin n → Fin (N.access j).dim) (Fin n → Fin (N.access j).dim) ℂ
  povm : ∀ j, IsPOVM (decode j)
  in_algebra : ∀ j mu, InBlockPower (N.access j).block n (decode j mu)

/-- PDF p.2: bits per use. Codes carry the positive length and message-cardinality guards. -/
def codeRate {s r n : ℕ} {C : ClassicalChannel s} {N : Network C r}
    (c : MultiwayBlockCode N n) (i : Fin s) : ℝ :=
  Real.logb 2 (c.messages i : ℝ) / n

/-- PDF p.2: probability of any incorrectly decoded sender message, uniformly averaged
on the entire independent message tuple, separately for each receiver. -/
def averageTupleError {s r n : ℕ} {C : ClassicalChannel s} {N : Network C r}
    (c : MultiwayBlockCode N n) (j : Fin r) : ℝ :=
  1 - (Fintype.card (∀ i, Fin (c.messages i)) : ℝ)⁻¹ *
    ∑ mu : (∀ i, Fin (c.messages i)),
      effectProb (piSuperop (fun _ : Fin n => fun T => (N.access j).embed T) (c.decode j mu))
        (blockOutput C n (fun i => c.encode i (mu i)))

/-- PDF p.2: nonnegative operational achievable rates, with codes for every sufficiently
large positive length, and average error at every receiver. -/
def capacityRegion {s r : ℕ} {C : ClassicalChannel s} (N : Network C r) :
    Set (Fin s → ℝ) :=
  {R | (∀ i, 0 ≤ R i) ∧ ∀ epsilon delta : ℝ, 0 < epsilon → 0 < delta →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∃ c : MultiwayBlockCode N n, (∀ j, averageTupleError c j ≤ epsilon) ∧
        ∀ i, R i - delta ≤ codeRate c i}

/-- PDF p.2: actual concatenation, including a common pairing of messages at every
receiver and tensor-product decoding on the two subblocks. -/
def IsConcatenation {s r m n : ℕ} {C : ClassicalChannel s} {N : Network C r}
    (c : MultiwayBlockCode N m) (d : MultiwayBlockCode N n) (e : MultiwayBlockCode N (m + n)) : Prop :=
  ∃ pair : ∀ i, Fin (e.messages i) ≃ Fin (c.messages i) × Fin (d.messages i),
    (∀ i mu k, e.encode i mu k =
      Fin.addCases (c.encode i (pair i mu).1) (d.encode i (pair i mu).2) k) ∧
    ∀ j mu a b, e.decode j mu a b =
      c.decode j (fun i => (pair i (mu i)).1)
        (fun k => a (Fin.castAdd n k)) (fun k => b (Fin.castAdd n k)) *
      d.decode j (fun i => (pair i (mu i)).2)
        (fun k => a (Fin.natAdd m k)) (fun k => b (Fin.natAdd m k))

/-- PDF p.2: coordinates of the senders in a subset, including the empty subset. -/
abbrev Letters {s : ℕ} (X : Fin s → ℕ) (J : Finset (Fin s)) :=
  ∀ i : {i : Fin s // i ∈ J}, Fin (X i.val)

/-- PDF pp.2-3: one independent a priori law for each sender; zeros are permitted. -/
abbrev InputLaw {s : ℕ} (X : Fin s → ℕ) := ∀ i, PMF (Fin (X i))

/-- PDF p.2: product marginal probability on a subset of sender registers. -/
def senderMarginalWeight {s : ℕ} {X : Fin s → ℕ} (P : InputLaw X)
    (J : Finset (Fin s)) (a : Letters X J) : ℝ :=
  ∏ i : {i : Fin s // i ∈ J}, (P i.val (a i)).toReal

/-- PDF p.2: full independent input probability. -/
def inputWeight {s : ℕ} {X : Fin s → ℕ} (P : InputLaw X)
    (x : ∀ i, Fin (X i)) : ℝ := ∏ i, (P i (x i)).toReal

/-- PDF p.2: matching the retained classical registers when tracing out the rest. -/
def Matches {s : ℕ} {X : Fin s → ℕ} (J : Finset (Fin s))
    (x : ∀ i, Fin (X i)) (a : Letters X J) : Prop :=
  ∀ i : {i : Fin s // i ∈ J}, x i.val = a i

/-- PDF pp.2-3: classical marginal of the channel state, computed from the input law. -/
def classicalMarginal {s : ℕ} {X : Fin s → ℕ} (P : InputLaw X)
    (J : Finset (Fin s)) : Matrix (Letters X J) (Letters X J) ℂ :=
  Matrix.diagonal (fun a => (senderMarginalWeight P J a : ℂ))

/-- PDF pp.2-3: the marginal gamma_{X(J)Y}, with every omitted input summed out. -/
def channelMarginal {s d : ℕ} {X : Fin s → ℕ}
    (W : (∀ i, Fin (X i)) → Matrix (Fin d) (Fin d) ℂ)
    (P : InputLaw X) (J : Finset (Fin s)) :
    Matrix (Letters X J × Fin d) (Letters X J × Fin d) ℂ :=
  fun a b => if a.1 = b.1 then
    ∑ x : (∀ i, Fin (X i)), if Matches J x a.1 then
      (inputWeight P x : ℂ) * W x a.2 b.2 else 0
    else 0

/-- PDF p.3: H(X(J)), in bits, with intrinsic trace. -/
def classicalEntropy {s : ℕ} {X : Fin s → ℕ} (P : InputLaw X)
    (J : Finset (Fin s)) : ℝ := vnEntropy (classicalMarginal P J)

/-- PDF p.3: H(Y X(J)), in bits, from the computed channel-state marginal. -/
def jointEntropy {s d : ℕ} {X : Fin s → ℕ}
    (W : (∀ i, Fin (X i)) → Matrix (Fin d) (Fin d) ℂ)
    (P : InputLaw X) (J : Finset (Fin s)) : ℝ := vnEntropy (channelMarginal W P J)

/-- PDF p.3: H(Y|X(J)) = H(YX(J)) - H(X(J)). -/
def conditionalOutputEntropy {s d : ℕ} {X : Fin s → ℕ}
    (W : (∀ i, Fin (X i)) → Matrix (Fin d) (Fin d) ℂ)
    (P : InputLaw X) (J : Finset (Fin s)) : ℝ :=
  jointEntropy W P J - classicalEntropy P J

/-- PDF p.3: conditional mutual information, defined by the four entropy terms,
rather than assuming the independence identity asserted in the theorem. -/
def conditionalInformation {s d : ℕ} {X : Fin s → ℕ}
    (W : (∀ i, Fin (X i)) → Matrix (Fin d) (Fin d) ℂ)
    (P : InputLaw X) (J : Finset (Fin s)) : ℝ :=
  classicalEntropy P Finset.univ + jointEntropy W P Jᶜ -
    jointEntropy W P Finset.univ - classicalEntropy P Jᶜ

/-- PDF pp.3,7: I(X(J) : Y X(K)); used only with disjoint J,K. -/
def senderOutputMutualInformation {s d : ℕ} {X : Fin s → ℕ}
    (W : (∀ i, Fin (X i)) → Matrix (Fin d) (Fin d) ℂ)
    (P : InputLaw X) (J K : Finset (Fin s)) : ℝ :=
  classicalEntropy P J + jointEntropy W P K - jointEntropy W P (J ∪ K)

/-- PDF p.2: P_J W averages precisely J; the remaining argument is J-complement. -/
def averagedChannel {s d : ℕ} {X : Fin s → ℕ}
    (W : (∀ i, Fin (X i)) → Matrix (Fin d) (Fin d) ℂ)
    (P : InputLaw X) (J : Finset (Fin s)) (a : Letters X Jᶜ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ x : (∀ i, Fin (X i)), if Matches Jᶜ x a then
    ((∏ i ∈ J, (P i (x i)).toReal : ℝ) : ℂ) • W x else 0

/-- PDF p.3: H(P_J W | P_{J-complement}), an average over the remaining inputs. -/
def averagedChannelEntropy {s d : ℕ} {X : Fin s → ℕ}
    (W : (∀ i, Fin (X i)) → Matrix (Fin d) (Fin d) ℂ)
    (P : InputLaw X) (J : Finset (Fin s)) : ℝ :=
  ∑ a : Letters X Jᶜ, senderMarginalWeight P Jᶜ a * vnEntropy (averagedChannel W P J a)

/-- PDF p.3: H(W|P_[s]), averaging entropy of the original channel outputs. -/
def meanOutputEntropy {s d : ℕ} {X : Fin s → ℕ}
    (W : (∀ i, Fin (X i)) → Matrix (Fin d) (Fin d) ℂ)
    (P : InputLaw X) : ℝ :=
  ∑ x : (∀ i, Fin (X i)), inputWeight P x * vnEntropy (W x)

/-- PDF pp.4,6: the fixed-product-law single-letter rate polytope. Every subset,
including empty and full, is tested. -/
def productLawRateRegion {s : ℕ} (C : ClassicalChannel s) (P : InputLaw C.alphabet) :
    Set (Fin s → ℝ) :=
  {R | (∀ i, 0 ≤ R i) ∧ ∀ J : Finset (Fin s),
    ∑ i ∈ J, R i ≤ conditionalInformation C.state P J}

/-- PDF p.3, theorem 3: one mixture, chosen before both sender subset and receiver.
All channel states use the SAME channel, with product laws conditional on the mixture label. -/
def MixtureDominates {s r : ℕ} {C : ClassicalChannel s} (N : Network C r)
    (R : Fin s → ℝ) (k : ℕ) : Prop :=
  ∃ q : PMF (Fin k), ∃ P : Fin k → InputLaw C.alphabet,
    ∀ (J : Finset (Fin s)) (j : Fin r),
      ∑ i ∈ J, R i ≤ ∑ u : Fin k, (q u).toReal *
        conditionalInformation (fun x => restrictedState (N.access j) (C.state x)) (P u) J

/-- PDF p.3: preclosure outer region; nonnegativity is not lost on convexification. -/
def mixtureRegion {s r : ℕ} {C : ClassicalChannel s} (N : Network C r) :
    Set (Fin s → ℝ) := {R | (∀ i, 0 ≤ R i) ∧ ∃ k : ℕ, MixtureDominates N R k}

/-- PDF p.7: extreme point AND maximal for the coordinatewise order, in the fixed-law
polytope. This excludes the origin when some positive rate is possible. -/
def IsUpperExtreme {s : ℕ} (S : Set (Fin s → ℝ)) (R : Fin s → ℝ) : Prop :=
  R ∈ S ∧
    (∀ a ∈ S, ∀ b ∈ S, ∀ t : ℝ, 0 < t → t < 1 →
      R = t • a + (1 - t) • b → a = R ∧ b = R) ∧
    ∀ a ∈ S, (∀ i, R i ≤ a i) → a = R

/-- PDF p.7: a permutation's preceding classical registers; none precedes index zero. -/
def predecessors {s : ℕ} (pi : Equiv.Perm (Fin s)) (i : Fin s) : Finset (Fin s) :=
  (Finset.univ.filter fun j => j < i).image pi

/-- PDF p.7: permutation rate tuple, computed by the information formula on the page. -/
def permutationRates {s : ℕ} (C : ClassicalChannel s) (P : InputLaw C.alphabet)
    (pi : Equiv.Perm (Fin s)) : Fin s → ℝ :=
  fun a => senderOutputMutualInformation C.state P {a} (predecessors pi (pi.symm a))

/-- PDF p.4: the positive square-root (Luders) measurement branch. -/
def ludersBranch {B : Type*} {d : ℕ} (D : B → Matrix (Fin d) (Fin d) ℂ)
    (rho : Matrix (Fin d) (Fin d) ℂ) (b : B) : Matrix (Fin d) (Fin d) ℂ :=
  cfc Real.sqrt (D b) * rho * cfc Real.sqrt (D b)

/-- PDF p.4, lemma 7: the actual nonselective square-root operation delta. -/
def tenderOperation {B : Type*} [Fintype B] {d : ℕ}
    (D : B → Matrix (Fin d) (Fin d) ℂ) (rho : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := ∑ b, ludersBranch D rho b

/-- PDF p.4, lemma 7: Delta, retaining the actual classical measurement outcome. -/
def labelledOperation {B : Type*} [DecidableEq B] {d : ℕ}
    (D : B → Matrix (Fin d) (Fin d) ℂ) (rho : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (B × Fin d) (B × Fin d) ℂ :=
  fun a b => if a.1 = b.1 then ludersBranch D rho a.1 a.2 b.2 else 0

/-- PDF p.4: the ideal classical label tensored with an undisturbed state. -/
def idealLabel {B : Type*} [DecidableEq B] {d : ℕ} (b : B)
    (rho : Matrix (Fin d) (Fin d) ℂ) : Matrix (B × Fin d) (B × Fin d) ℂ :=
  fun a c => if a.1 = b ∧ c.1 = b then rho a.2 c.2 else 0

/-! Sanity examples: intrinsic blocks, normalization, the memoryless empty block,
receiver access, independent probabilities, information definitions, permutation ordering,
and the actual square-root instrument. These examples contain no admitted proofs. -/

example {d : ℕ} (block : Fin d → ℕ) : InBlocks block (0 : Matrix (Fin d) (Fin d) ℂ) := by
  intro a b h
  rfl

example {d : ℕ} (block : Fin d → ℕ) : InBlocks block (1 : Matrix (Fin d) (Fin d) ℂ) := by
  intro a b h
  have hab : a ≠ b := fun e => h (congrArg block e)
  simp [Matrix.one_apply, hab]

example {d : ℕ} (block : Fin d → ℕ) (n : ℕ) :
    InBlockPower block n (0 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) := by
  intro a b h
  rfl

example {s : ℕ} (C : ClassicalChannel s) (x : ∀ i, Fin (C.alphabet i)) :
    (C.state x).trace = 1 := (C.normalized x).2

example {s : ℕ} (C : ClassicalChannel s) : (fullAccess C).embed 1 = 1 := rfl

example {s : ℕ} (C : ClassicalChannel s) : (singleReceiver C).access 0 = fullAccess C := rfl

example {s : ℕ} {C : ClassicalChannel s} (A : Access C)
    (rho : Matrix (Fin C.output) (Fin C.output) ℂ) (a : Fin A.dim) :
    restrictedState A rho a a = (rho * A.embed (Matrix.single a a 1)).trace := by
  simp [restrictedState]

example {s : ℕ} (C : ClassicalChannel s)
    (word : ∀ i, Fin 0 → Fin (C.alphabet i)) (a b : Fin 0 → Fin C.output) :
    blockOutput C 0 word a b = 1 := by
  simp [blockOutput]

example {d e : ℕ} (E : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin e) (Fin e) ℂ)
    (n : ℕ) : piSuperop (fun _ : Fin n => E) 0 = 0 := by
  ext a b
  simp [piSuperop]

example {s r n : ℕ} {C : ClassicalChannel s} {N : Network C r} (c : MultiwayBlockCode N n) :
    0 < n ∧ ∀ i, 0 < c.messages i := ⟨c.length_pos, c.messages_pos⟩

example {s r n : ℕ} {C : ClassicalChannel s} {N : Network C r} (c : MultiwayBlockCode N n) (i : Fin s) :
    codeRate c i = Real.logb 2 (c.messages i : ℝ) / n := rfl

example {s r : ℕ} {C : ClassicalChannel s} (N : Network C r)
    (R : Fin s → ℝ) (h : R ∈ capacityRegion N) : ∀ i, 0 ≤ R i := h.1

example {s : ℕ} {X : Fin s → ℕ} (P : InputLaw X) (a : Letters X ∅) :
    senderMarginalWeight P ∅ a = 1 := by
  simp [senderMarginalWeight]

example {s : ℕ} {X : Fin s → ℕ} (x : ∀ i, Fin (X i)) (a : Letters X ∅) :
    Matches (X := X) (∅ : Finset (Fin s)) x a := by
  change ∀ i : {i : Fin s // i ∈ (∅ : Finset (Fin s))}, x i.val = a i
  intro i
  exact (Finset.notMem_empty i.val i.property).elim

example {s d : ℕ} {X : Fin s → ℕ}
    (W : (∀ i, Fin (X i)) → Matrix (Fin d) (Fin d) ℂ)
    (P : InputLaw X) (J : Finset (Fin s)) :
    conditionalOutputEntropy W P J = jointEntropy W P J - classicalEntropy P J := rfl

example {s d : ℕ} {X : Fin s → ℕ}
    (W : (∀ i, Fin (X i)) → Matrix (Fin d) (Fin d) ℂ)
    (P : InputLaw X) (a b : Letters X (Finset.univ : Finset (Fin s))) :
    classicalMarginal P Finset.univ a b =
      Matrix.diagonal (fun z => (senderMarginalWeight P Finset.univ z : ℂ)) a b := rfl

example {s : ℕ} (C : ClassicalChannel s) (P : InputLaw C.alphabet) (R : Fin s → ℝ)
    (h : R ∈ productLawRateRegion C P) : ∀ i, 0 ≤ R i := h.1

example {s r : ℕ} {C : ClassicalChannel s} (N : Network C r) (R : Fin s → ℝ)
    (h : R ∈ mixtureRegion N) : ∃ k, MixtureDominates N R k := h.2

example {s : ℕ} (S : Set (Fin s → ℝ)) (R : Fin s → ℝ)
    (h : IsUpperExtreme S R) : R ∈ S := h.1

example {s : ℕ} (pi : Equiv.Perm (Fin (s + 1))) : predecessors pi 0 = ∅ := by
  simp [predecessors]

example {s : ℕ} (C : ClassicalChannel s) (P : InputLaw C.alphabet)
    (pi : Equiv.Perm (Fin s)) (i : Fin s) :
    permutationRates C P pi (pi i) =
      senderOutputMutualInformation C.state P {pi i} (predecessors pi i) := by
  simp [permutationRates]

example {B : Type*} {d : ℕ} (D : B → Matrix (Fin d) (Fin d) ℂ) (b : B) :
    ludersBranch D 0 b = 0 := by
  simp [ludersBranch]

example {B : Type*} [Fintype B] {d : ℕ} (D : B → Matrix (Fin d) (Fin d) ℂ) :
    tenderOperation D 0 = 0 := by
  simp [tenderOperation, ludersBranch]

example {B : Type*} [DecidableEq B] {d : ℕ}
    (D : B → Matrix (Fin d) (Fin d) ℂ) (rho : Matrix (Fin d) (Fin d) ℂ)
    (b : B) (i j : Fin d) :
    labelledOperation D rho (b, i) (b, j) = ludersBranch D rho b i j := by
  simp [labelledOperation]

example {B : Type*} [DecidableEq B] {d : ℕ} (b : B)
    (rho : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    idealLabel b rho (b, i) (b, j) = rho i j := by
  simp [idealLabel]

/-- A measurement with the sole effect I leaves every input exactly unchanged. -/
example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) :
    tenderOperation (fun _ : Unit => (1 : Matrix (Fin d) (Fin d) ℂ)) rho = rho := by
  simp [tenderOperation, ludersBranch, cfc_one]

/-- Recording that deterministic outcome preserves the entire input matrix. -/
example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    labelledOperation (fun _ : Unit => (1 : Matrix (Fin d) (Fin d) ℂ)) rho
      ((), i) ((), j) = rho i j := by
  simp [labelledOperation, ludersBranch, cfc_one]

end QAlgorithms.Papers.Independent.Claimed50.P40


