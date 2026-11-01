-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P63
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P63
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:11:59.209466+00:00
-- url     : https://prove2.me/theorems/00c25747-5f5b-4320-9048-208e0702835e
-- title:
--   Definitions for Weak locking capacity of quantum channels can be much larger than private capacity
-- statement:
--   The objects the formalized statements of *Weak locking capacity of quantum channels can be much larger than private capacity* (arXiv:1403.6361) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `jointConditionalBits`: PDF p.5: H(I|J); zero-probability columns contribute zero.
--   - `measuredEnsembleJoint`: PDF p.5: the joint law p_i Tr(rho_i Q_j).
--   - `ensembleConditionalBits`: PDF p.8: conditional Shannon entropy of an ensemble measured with Q.
--   - `accessibleEquivocation`: PDF p.5: optimization over every finite POVM, including joint measurements. For normalized data the set is nonempty and contained in [0,log |I|].
--   - `optimizedEquivocation`: PDF pp.5,7: optimization over all priors, including zero weights.
--   - `measurementWorstPrior`: PDF p.8: opposite optimization order in the minimax formula.
--   - `taggedEffects`: PDF p.8: random measurement mixing RETAINS the branch label.
--   - `averageState`: PDF pp.7,9: ensemble average state.
--   - `supportInvSqrt`: PDF pp.7,9: support inverse square root, with zero eigenvalues mapped to zero.
--   - `associatedEffects`: PDF pp.7,9: associated effects, summing to the average state's support projector.
--   - `povmMinimumShannon`: PDF p.8: minimum output entropy of an ordinary normalized POVM.
--   - `associatedMinimum`: PDF pp.7,9–10: associated POVM minimum on supp(rho-bar), excluding the kernel. No invertibility hypothesis or arbitrary kernel completion is introduced.
--   - `stateMinBits`: PDF p.9, Definition 7: min-entropy of a normalized density.
--   - `traceSmoothStateMinBits`: PDF p.9: smoothing over NORMALIZED states at HALF trace norm distance.
--   - `conditionalMinBits`: PDF p.9: conditional min-entropy, optimizing a normalized conditioning density. The accepted extended exponent optimization is finite on normalized states; toReal keeps its value. Zero/subnormalized off-domain values are not asserted here.
--   - `marginalMinEntropy`: PDF p.9: the actual marginal reference, with its support inverse.
--   - `traceSmoothConditionalMinBits`: PDF p.9: normalized bipartite smoothing, without fixing the marginal.
--   - `qcBranchDensity`: PDF p.9: qc-state with the classical register SECOND.
--   - `classicalJoint`: PDF p.9: a classical joint law represented by its diagonal density.
--   - `tensorEffects`: PDF p.8: product measurement on arbitrary, possibly entangled, input states.
--   - `measuredState`: PDF p.8: classical output density of a product measurement.
--   - `iidJoint`: PDF p.9: IID labels, with an unrestricted collective measurement on E^n.
--   - `environment`: PDF p.2: environment's partial trace of the SAME dilation.
--   - `KeyedBlockCode`: PDF pp.2–3: keyed code, normalized mixed encodings and a POVM for each key. Both message and independent key are uniform. The key count is positive, and each accepted branch enforces positive message count, density signals and a POVM.
--   - `keyedAverageError`: PDF p.2, (1): decoding error averaged over messages and independent secret key.
--   - `averagedSignal`: PDF p.3: Eve sees key-averaged signal states.
--   - `WeakSecure`: PDF p.2, (3): full l1 norm; EVERY POVM has ONE message-independent law.
--   - `PrivateSecure`: PDF p.2, (2): full trace norm, with NO one-half factor.
--   - `messageRateBits`: PDF p.3: rate per channel use, indexing positive lengths by n+1.
--   - `keyRate`: PDF p.3: secret bits per channel use.
--   - `KeyedRateAtLeast`: PDF p.3: limiting inferior rate at least R, allowing arbitrary rate slack.
--   - `ReliableKeyedSequence`: PDF p.3: reliability and a sublinear preshared uniform secret.
--   - `KeyedAchievable`: PDF p.3: operational nonnegative achievable rates for the selected security criterion.
--   - `keyedCapacity`: PDF p.3: supremum of achievable nonnegative rates. For valid finite channels it is a nonempty bounded set; no feedback or free discussion is present in these codes.
--   - `CqComplement`: PDF p.5, (5): cq complement in the specified computational input basis.
--   - `twoBasisVector`: PDF p.11: computational and discrete Fourier basis vectors.
--   - `twoBasisDilation`: PDF p.11, Example 12: 2d-dimensional input and receiver, d-dimensional environment.
--   - `upperInformation`: PDF pp.5,14, (8): L_W^(u), over arbitrary finite mixed input ensembles. I_acc = H(p) - S_acc; this uses the same measurement optimization as above.
--   - `activatedReceiver`: PDF p.15: N tensor id_k, retaining off-diagonal auxiliary blocks.
--   - `activatedEnvironment`: PDF p.15: the noiseless factor leaks nothing; Eve receives only N^c.
--   - `activatedCapacity`: PDF p.15: amortized capacity, with positive noiseless dimension and log k charge.
--   - `regularizedUpper`: PDF p.15: regularized upper information, over positive block lengths.
--   - `arimotoOutput`: PDF p.14: Arimoto conditional alpha entropy of measured ensemble branches.
--   - `constrainedRenyi`: PDF p.14: constrained minimum over all finite decompositions with average sigma.
--   - `ConstrainedRenyiAdditivity`: PDF p.14, (16): the GLOBAL conjecture, not an asserted fact or scalar placeholder. Fin enumerations cover every finite-dimensional system and outcome space.
--   - `IIDUncertainty`: PDF p.14, (17): global uniform eventual IID uncertainty, with arbitrary rate slack. The threshold precedes Eve's collective POVM. Arbitrarily small fixed epsilon permits vanishing errors by diagonal choice. This predicate is a conjectural premise.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, https://arxiv.org/abs/1403.6361v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Learning
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

/-! Winter, arXiv:1403.6361v3. Imported accepted primitives and paper-local operational
and entropy interfaces. Names distinguish Winter's keyed and normalized-trace conventions.
All logarithms are binary. Compilation is pending the batch mechanical handoff.
The three plan deferrals are documented in HARD.md. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P63

open QAlgorithms Filter
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)
open QAlgorithms.Papers.Independent.Information100.P71 (channelPower dilationMap SupportIncluded)
open QAlgorithms.Papers.Independent.Bridge50.P47 (SymmetricIndex universalSymmetricDilation)
open QAlgorithms.Learning (IsDistribution)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5: H(I|J); zero-probability columns contribute zero. -/
def jointConditionalBits {I J : Type} [Fintype I] [Fintype J] (P : I → J → ℝ) : ℝ :=
  -∑ j, ∑ i, P i j * Real.logb 2 (P i j / ∑ k, P k j)

/-- PDF p.5: the joint law p_i Tr(rho_i Q_j). -/
def measuredEnsembleJoint {I E J : Type} [Fintype E] (p : I → ℝ) (rho : I → Mat E)
    (Q : J → Mat E) : I → J → ℝ :=
  fun i j => p i * effectProb (Q j) (rho i)

/-- PDF p.8: conditional Shannon entropy of an ensemble measured with Q. -/
def ensembleConditionalBits {I E J : Type} [Fintype I] [Fintype E] [Fintype J]
    (p : I → ℝ) (rho : I → Mat E) (Q : J → Mat E) : ℝ :=
  jointConditionalBits (measuredEnsembleJoint p rho Q)

/-- PDF p.5: optimization over every finite POVM, including joint measurements.
For normalized data the set is nonempty and contained in [0,log |I|]. -/
def accessibleEquivocation {I E : Type} [Fintype I] [Fintype E] [DecidableEq E]
    (p : I → ℝ) (rho : I → Mat E) : ℝ :=
  sInf {h | ∃ Q : Measurement E, h = ensembleConditionalBits p rho Q.effect}

/-- PDF pp.5,7: optimization over all priors, including zero weights. -/
def optimizedEquivocation {I E : Type} [Fintype I] [Fintype E] [DecidableEq E]
    (rho : I → Mat E) : ℝ :=
  sSup {h | ∃ p : I → ℝ, IsDistribution p ∧ h = accessibleEquivocation p rho}

/-- PDF p.8: opposite optimization order in the minimax formula. -/
def measurementWorstPrior {I E : Type} [Fintype I] [Fintype E] [DecidableEq E]
    (rho : I → Mat E) (Q : Measurement E) : ℝ :=
  sSup {h | ∃ p : I → ℝ, IsDistribution p ∧ h = ensembleConditionalBits p rho Q.effect}

/-- PDF p.8: random measurement mixing RETAINS the branch label. -/
def taggedEffects {E J K : Type} (lambda : ℝ) (Q : J → Mat E) (R : K → Mat E) :
    J ⊕ K → Mat E :=
  Sum.elim (fun j => (lambda : ℂ) • Q j) (fun k => ((1 - lambda : ℝ) : ℂ) • R k)

/-- PDF pp.7,9: ensemble average state. -/
def averageState {I E : Type} [Fintype I] (p : I → ℝ) (rho : I → Mat E) : Mat E :=
  ∑ i, (p i : ℂ) • rho i

/-- PDF pp.7,9: support inverse square root, with zero eigenvalues mapped to zero. -/
def supportInvSqrt {E : Type} [Fintype E] [DecidableEq E] (rho : Mat E) : Mat E :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) rho

/-- PDF pp.7,9: associated effects, summing to the average state's support projector. -/
def associatedEffects {I E : Type} [Fintype I] [Fintype E] [DecidableEq E]
    (p : I → ℝ) (rho : I → Mat E) (i : I) : Mat E :=
  supportInvSqrt (averageState p rho) * ((p i : ℂ) • rho i) *
    supportInvSqrt (averageState p rho)

/-- PDF p.8: minimum output entropy of an ordinary normalized POVM. -/
def povmMinimumShannon {E I : Type} [Fintype E] [Fintype I] (M : I → Mat E) : ℝ :=
  sInf {h | ∃ psi : Mat E, IsDensityMatrix psi ∧
    h = shannon (fun i => effectProb (M i) psi)}

/-- PDF pp.7,9–10: associated POVM minimum on supp(rho-bar), excluding the kernel.
No invertibility hypothesis or arbitrary kernel completion is introduced. -/
def associatedMinimum {I E : Type} [Fintype I] [Fintype E] [DecidableEq E]
    (p : I → ℝ) (rho : I → Mat E) : ℝ :=
  sInf {h | ∃ psi : Mat E, IsDensityMatrix psi ∧ SupportIncluded psi (averageState p rho) ∧
    h = shannon (fun i => effectProb (associatedEffects p rho i) psi)}

/-- PDF p.9, Definition 7: min-entropy of a normalized density. -/
def stateMinBits {A : Type} [Fintype A] [DecidableEq A] (rho : Mat A) : ℝ :=
  -Real.logb 2 (specNorm rho)

/-- PDF p.9: smoothing over NORMALIZED states at HALF trace norm distance. -/
def traceSmoothStateMinBits {A : Type} [Fintype A] [DecidableEq A]
    (eps : ℝ) (rho : Mat A) : ℝ :=
  sSup {h | ∃ r : Mat A, IsDensityMatrix r ∧ traceNorm (rho - r) / 2 ≤ eps ∧
    h = stateMinBits r}

/-- PDF p.9: conditional min-entropy, optimizing a normalized conditioning density.
The accepted extended exponent optimization is finite on normalized states; toReal
keeps its value. Zero/subnormalized off-domain values are not asserted here. -/
def conditionalMinBits {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Mat (A × B)) : ℝ :=
  (QAlgorithms.Papers.Independent.Information100.P67.conditionalMinEntropy rho).toReal

/-- PDF p.9: the actual marginal reference, with its support inverse. -/
def marginalMinEntropy {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Mat (A × B)) : ℝ :=
  let S := Matrix.kronecker (1 : Mat A) (supportInvSqrt (traceLeft rho));
  -Real.logb 2 (specNorm (S * rho * S))

/-- PDF p.9: normalized bipartite smoothing, without fixing the marginal. -/
def traceSmoothConditionalMinBits {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (eps : ℝ) (rho : Mat (A × B)) : ℝ :=
  sSup {h | ∃ r : Mat (A × B), IsDensityMatrix r ∧ traceNorm (rho - r) / 2 ≤ eps ∧
    h = conditionalMinBits r}

/-- PDF p.9: qc-state with the classical register SECOND. -/
def qcBranchDensity {A J : Type} [DecidableEq J] (q : J → ℝ) (rho : J → Mat A) : Mat (A × J) :=
  fun x y => if x.2 = y.2 then (q x.2 : ℂ) * rho x.2 x.1 y.1 else 0

/-- PDF p.9: a classical joint law represented by its diagonal density. -/
def classicalJoint {I J : Type} [DecidableEq I] [DecidableEq J]
    (P : I → J → ℝ) : Mat (I × J) :=
  Matrix.diagonal (fun x => (P x.1 x.2 : ℂ))

/-- PDF p.8: product measurement on arbitrary, possibly entangled, input states. -/
def tensorEffects {E I : Type} (M : I → Mat E) (n : ℕ) :
    (Fin n → I) → Mat (Fin n → E) :=
  fun i x y => ∏ t, M (i t) (x t) (y t)

/-- PDF p.8: classical output density of a product measurement. -/
def measuredState {E I : Type} [Fintype E] [DecidableEq I]
    (M : I → Mat E) (n : ℕ) (psi : Mat (Fin n → E)) : Mat (Fin n → I) :=
  Matrix.diagonal (fun i => (effectProb (tensorEffects M n i) psi : ℂ))

/-- PDF p.9: IID labels, with an unrestricted collective measurement on E^n. -/
def iidJoint {I E : Type} [Fintype E] [DecidableEq E]
    (p : I → ℝ) (rho : I → Mat E) (n : ℕ) (Q : Measurement (Fin n → E)) :
    (Fin n → I) → Fin Q.outcomes → ℝ :=
  fun i j => (∏ t, p (i t)) * effectProb (Q.effect j) (fun x y => ∏ t, rho (i t) (x t) (y t))

/-- PDF p.2: environment's partial trace of the SAME dilation. -/
def environment {A B E : Type} [Fintype A] [Fintype B]
    (V : Matrix (B × E) A ℂ) : Superop A E :=
  fun rho => traceLeft (V * rho * Vᴴ)

/-- PDF pp.2–3: keyed code, normalized mixed encodings and a POVM for each key.
Both message and independent key are uniform. The key count is positive, and
each accepted branch enforces positive message count, density signals and a POVM. -/
structure KeyedBlockCode (A B : Type) [Fintype A] [Fintype B] [DecidableEq B] (n : ℕ) where
  messages : ℕ
  keys : ℕ
  keys_pos : 0 < keys
  branch : Fin keys →
    QAlgorithms.Papers.Independent.Information100.P63.Code (Fin n → A) (Fin n → B) messages

/-- PDF p.2, (1): decoding error averaged over messages and independent secret key. -/
def keyedAverageError {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : Superop A B) {n : ℕ} (C : KeyedBlockCode A B n) : ℝ :=
  ((C.keys : ℝ) * C.messages)⁻¹ *
    ∑ k, ∑ m, (1 - effectProb ((C.branch k).measurement m) (channelPower N n ((C.branch k).word m)))

/-- PDF p.3: Eve sees key-averaged signal states. -/
def averagedSignal {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    {n : ℕ} (C : KeyedBlockCode A B n) (m : Fin C.messages) : Mat (Fin n → A) :=
  ((C.keys : ℂ)⁻¹) • ∑ k, (C.branch k).word m

/-- PDF p.2, (3): full l1 norm; EVERY POVM has ONE message-independent law. -/
def WeakSecure {A B E : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype E] [DecidableEq E]
    (Nc : Superop A E) {n : ℕ} (C : KeyedBlockCode A B n) (delta : ℝ) : Prop :=
  ∀ Q : Measurement (Fin n → E), ∃ omega : Fin Q.outcomes → ℝ, IsDistribution omega ∧
    (C.messages : ℝ)⁻¹ * ∑ m, ∑ j,
      |effectProb (Q.effect j) (channelPower Nc n (averagedSignal C m)) - omega j| ≤ delta

/-- PDF p.2, (2): full trace norm, with NO one-half factor. -/
def PrivateSecure {A B E : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype E] [DecidableEq E]
    (Nc : Superop A E) {n : ℕ} (C : KeyedBlockCode A B n) (delta : ℝ) : Prop :=
  ∃ omega : Mat (Fin n → E), IsDensityMatrix omega ∧
    (C.messages : ℝ)⁻¹ * ∑ m,
      traceNorm (channelPower Nc n (averagedSignal C m) - omega) ≤ delta

/-- PDF p.3: rate per channel use, indexing positive lengths by n+1. -/
def messageRateBits {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    {n : ℕ} (C : KeyedBlockCode A B (n + 1)) : ℝ :=
  Real.logb 2 C.messages / (n + 1)

/-- PDF p.3: secret bits per channel use. -/
def keyRate {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    {n : ℕ} (C : KeyedBlockCode A B (n + 1)) : ℝ :=
  Real.logb 2 C.keys / (n + 1)

/-- PDF p.3: limiting inferior rate at least R, allowing arbitrary rate slack. -/
def KeyedRateAtLeast {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (C : (n : ℕ) → KeyedBlockCode A B (n + 1)) (R : ℝ) : Prop :=
  ∀ slack > (0 : ℝ), ∀ᶠ n in atTop, R - slack ≤ messageRateBits (C n)

/-- PDF p.3: reliability and a sublinear preshared uniform secret. -/
def ReliableKeyedSequence {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : Superop A B) (C : (n : ℕ) → KeyedBlockCode A B (n + 1)) : Prop :=
  Tendsto (fun n => keyRate (C n)) atTop (nhds 0) ∧
  Tendsto (fun n => keyedAverageError N (C n)) atTop (nhds 0)

/-- PDF p.3: operational nonnegative achievable rates for the selected security criterion. -/
def KeyedAchievable {A B E : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] (N : Superop A B) (Nc : Superop A E)
    (weak : Bool) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ C : (n : ℕ) → KeyedBlockCode A B (n + 1), ReliableKeyedSequence N C ∧ KeyedRateAtLeast C R ∧
    ∀ eps > (0 : ℝ), ∀ᶠ n in atTop,
      if weak then WeakSecure Nc (C n) eps else PrivateSecure Nc (C n) eps

/-- PDF p.3: supremum of achievable nonnegative rates. For valid finite channels it
is a nonempty bounded set; no feedback or free discussion is present in these codes. -/
def keyedCapacity {A B E : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] (N : Superop A B) (Nc : Superop A E) (weak : Bool) : ℝ :=
  sSup {R | KeyedAchievable N Nc weak R}

/-- PDF p.5, (5): cq complement in the specified computational input basis. -/
def CqComplement {A E : Type} [Fintype A] [DecidableEq A] [Fintype E]
    (Nc : Superop A E) (rho : A → Mat E) : Prop :=
  (∀ i, IsDensityMatrix (rho i)) ∧
  ∀ i j, Nc (Matrix.single i j 1) = if i = j then rho i else 0

/-- PDF p.11: computational and discrete Fourier basis vectors. -/
def twoBasisVector (d : ℕ) (b : Bool) (i x : Fin d) : ℂ :=
  if b then (Real.sqrt d : ℂ)⁻¹ *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (i.val : ℂ) * (x.val : ℂ) / (d : ℂ))
  else if x = i then 1 else 0

/-- PDF p.11, Example 12: 2d-dimensional input and receiver, d-dimensional environment. -/
def twoBasisDilation (d : ℕ) : Matrix ((Bool × Fin d) × Fin d) (Bool × Fin d) ℂ :=
  fun out inp => if out.1 = inp then twoBasisVector d inp.1 inp.2 out.2 else 0

/-- PDF pp.5,14, (8): L_W^(u), over arbitrary finite mixed input ensembles.
I_acc = H(p) - S_acc; this uses the same measurement optimization as above. -/
def upperInformation {A B E : Type} [Fintype A] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] (N : Superop A B) (Nc : Superop A E) : ℝ :=
  sSup {h | ∃ m : ℕ, ∃ p : Fin m → ℝ, ∃ rho : Fin m → Mat A,
    IsDistribution p ∧ (∀ i, IsDensityMatrix (rho i)) ∧
    h = labelInformation p (fun i => N (rho i)) - shannon p +
      accessibleEquivocation p (fun i => Nc (rho i))}

/-- PDF p.15: N tensor id_k, retaining off-diagonal auxiliary blocks. -/
def activatedReceiver {A B : Type} (N : Superop A B) (k : ℕ) :
    Superop (A × Fin k) (B × Fin k) :=
  fun rho x y => N (fun a a' => rho (a, x.2) (a', y.2)) x.1 y.1

/-- PDF p.15: the noiseless factor leaks nothing; Eve receives only N^c. -/
def activatedEnvironment {A E : Type} (Nc : Superop A E) (k : ℕ) :
    Superop (A × Fin k) E :=
  fun rho => Nc (traceRight rho)

/-- PDF p.15: amortized capacity, with positive noiseless dimension and log k charge. -/
def activatedCapacity {A B E : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]
    (N : Superop A B) (Nc : Superop A E) : ℝ :=
  sSup {h | ∃ k : ℕ, 0 < k ∧ h =
    keyedCapacity (activatedReceiver N k) (activatedEnvironment Nc k) true - Real.logb 2 k}

/-- PDF p.15: regularized upper information, over positive block lengths. -/
def regularizedUpper {A B E : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]
    (N : Superop A B) (Nc : Superop A E) : ℝ :=
  sSup {h | ∃ n : ℕ, 0 < n ∧ h = upperInformation (channelPower N n) (channelPower Nc n) / n}

/-- PDF p.14: Arimoto conditional alpha entropy of measured ensemble branches. -/
def arimotoOutput {E I J : Type} [Fintype E] [Fintype I] [Fintype J]
    (alpha : ℝ) (M : I → Mat E) (q : J → ℝ) (psi : J → Mat E) : ℝ :=
  -alpha / (alpha - 1) * Real.logb 2
    (∑ j, q j * (∑ i, (effectProb (M i) (psi j)) ^ alpha) ^ (1 / alpha))

/-- PDF p.14: constrained minimum over all finite decompositions with average sigma. -/
def constrainedRenyi {E I : Type} [Fintype E] [Fintype I]
    (alpha : ℝ) (M : I → Mat E) (sigma : Mat E) : ℝ :=
  sInf {h | ∃ r : ℕ, ∃ q : Fin r → ℝ, ∃ psi : Fin r → Mat E,
    IsDistribution q ∧ (∀ j, IsDensityMatrix (psi j)) ∧ averageState q psi = sigma ∧
    h = arimotoOutput alpha M q psi}

/-- PDF p.14, (16): the GLOBAL conjecture, not an asserted fact or scalar placeholder.
Fin enumerations cover every finite-dimensional system and outcome space. -/
def ConstrainedRenyiAdditivity : Prop :=
  ∀ a b i j : ℕ, 0 < a → 0 < b →
  ∀ M : Fin i → Mat (Fin a), IsPOVM M →
  ∀ R : Fin j → Mat (Fin b), IsPOVM R →
  ∀ sigma : Mat (Fin a), IsDensityMatrix sigma →
  ∀ tau : Mat (Fin b), IsDensityMatrix tau → ∀ alpha : ℝ, 1 < alpha →
    constrainedRenyi alpha (fun x : Fin i × Fin j => Matrix.kronecker (M x.1) (R x.2))
      (Matrix.kronecker sigma tau) =
    constrainedRenyi alpha M sigma + constrainedRenyi alpha R tau

/-- PDF p.14, (17): global uniform eventual IID uncertainty, with arbitrary rate slack.
The threshold precedes Eve's collective POVM. Arbitrarily small fixed epsilon permits
vanishing errors by diagonal choice. This predicate is a conjectural premise. -/
def IIDUncertainty : Prop :=
  ∀ a e : ℕ, 0 < a → 0 < e → ∀ p : Fin a → ℝ, IsDistribution p →
  ∀ rho : Fin a → Mat (Fin e), (∀ i, IsDensityMatrix (rho i)) →
  ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ slack : ℝ, 0 < slack →
  ∃ n0 : ℕ, ∀ n ≥ n0, ∀ Q : Measurement (Fin n → Fin e),
    (n : ℝ) * (accessibleEquivocation p rho - slack) ≤
      traceSmoothConditionalMinBits eps (classicalJoint (iidJoint p rho n Q))

/-! Sanity examples pin deterministic entropy, a discarded tagged branch,
the empty tensor unit, and the diagonal symmetric normalization. -/

example : IsDistribution (fun _ : Fin 1 => (1 : ℝ)) := by
  constructor
  · intro i; norm_num
  · simp

example : shannon (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
  simp [shannon]

example {E J K : Type} (Q : J → Mat E) (R : K → Mat E) (k : K) :
    taggedEffects 1 Q R (Sum.inr k) = 0 := by
  simp [taggedEffects]

example {E I : Type} (M : I → Mat E) (i : Fin 0 → I) (x y : Fin 0 → E) :
    tensorEffects M 0 i x y = 1 := by
  simp [tensorEffects]

example (d : ℕ) (i : Fin d) : universalSymmetricDilation d (i, i) ⟨(i, i), le_refl i⟩ = 1 := by
  simp [universalSymmetricDilation]

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (n : ℕ) (C : KeyedBlockCode A B (n + 1)) (hm : C.messages = 1) : messageRateBits C = 0 := by
  simp [messageRateBits, hm]

/-- Reusing accepted code branches retains positive message count for every key. -/
example {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (n : ℕ) (C : KeyedBlockCode A B n) : 0 < C.messages := by
  exact (C.branch ⟨0, C.keys_pos⟩).positive

example {E : Type} [Fintype E] [DecidableEq E] :
    IsPOVM (fun _ : Fin 1 => (1 : Mat E)) := by
  exact ⟨fun _ => Matrix.PosSemidef.one, by simp⟩

example {E : Type} [Fintype E] [DecidableEq E] : supportInvSqrt (0 : Mat E) = 0 := by
  simp [supportInvSqrt, cfc_zero]

example {I E : Type} [Fintype I] [Fintype E] [DecidableEq E]
    (p : I → ℝ) (rho : I → Mat E) (i : I) (hi : p i = 0) :
    associatedEffects p rho i = 0 := by
  simp [associatedEffects, hi]

example {A J : Type} [DecidableEq J] (q : J → ℝ) (rho : J → Mat A)
    (a b : A) (j k : J) (hjk : j ≠ k) : qcBranchDensity q rho (a, j) (b, k) = 0 := by
  simp [qcBranchDensity, hjk]

example {A : Type} (k : ℕ) (rho : Mat (A × Fin k)) :
    activatedReceiver (fun X : Mat A => X) k rho = rho := by
  ext x y
  simp [activatedReceiver]

example (alpha : ℝ) :
    arimotoOutput alpha (fun _ : Fin 1 => (1 : Mat (Fin 1)))
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : Mat (Fin 1))) = 0 := by
  simp [arimotoOutput, effectProb, Matrix.trace]

end QAlgorithms.Papers.Independent.Intakenext100.P63


