-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P44
-- name    : QAlgorithms_Papers_Independent_Next46_P44
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:55:29.066116+00:00
-- url     : https://prove2.me/theorems/d9204239-6c4e-464f-9423-fd4728f35e18
-- title:
--   Definitions for Classical feedback for quantum channels
-- statement:
--   The objects the formalized statements of *Classical feedback for quantum channels* (arXiv:quant-ph/0409207) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `aepBadMass`: PDF p.3: probability of a block whose per-letter surprisal differs from h by more than e. Zero-mass words are excluded before their surprisal is used. The k=0 value is irrelevant to convergence at infinity. Logarithms are base two.
--   - `FiniteAEPSource`: PDF p.3: consistent normalized finite-alphabet block laws satisfying the AEP. Consistency is marginalization of the last letter; the AEP is convergence in probability of normalized base-two surprisal to the entropy rate.
--   - `replaceSubsystem`: PDF p.4: replace just the coordinates owned by a subsystem; every outside coordinate is held fixed, including outside off-diagonal matrix entries.
--   - `onSubsystem`: PDF p.4: an operation on exactly the indicated subsystem, identity on all other factors. This is the full blockwise extension to entangled inputs.
--   - `FeedbackProtocol`: PDF pp.2-4: fixed operations of an n-use feedback protocol on n designated input factors. Receiver instruments act on factors already transmitted, sender responses only on the strictly later factors. Outcomes use a common finite alphabet (unused outcomes may have zero Kraus operator). The maps have no message/codeword argument. The source decoder is deterministic postprocessing of the retained complete history; it does not change the quantum execution and is not needed for this Markov result.
--   - `FeedbackProtocol.step`: PDF p.4: one physical forward call, receiver outcome k, and sender response. At the last round the response acts on the empty tensor factor and is therefore trivial. Kraus branches remain subnormalized; no conditional division is performed.
--   - `FeedbackProtocol.branch`: PDF pp.4-5: execute all n rounds in order along history h, from the actual possibly entangled codeword density matrix. The branch trace is its probability.
--   - `FeedbackProtocol.receiver`: PDF pp.4-6: terminal receiver state, including an orthogonal record of every feedback outcome. All n physical systems have now been transmitted. Zero-probability histories remain zero operator blocks, without normalized fallback states.
--   - `terminalState`: PDF pp.3-6: the derived joint state of message, full classical codeword, and executed receiver. Registers are ordered M,(A,Z). Initially all physical factors belong to the sender; no shared resource or extra quantum register is supplied.
--   - `conditionalInfo`: PDF pp.5-6, with entropy convention p.2: I(M:Z|A) in bits from the four actual marginal entropies S(MA)+S(AZ)-S(A)-S(MAZ), for register order M,(A,Z).
-- source:
--   Classical feedback for quantum channels, arXiv:quant-ph/0409207v3, https://arxiv.org/abs/quant-ph/0409207v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement

/-!
Source: A. Skeen, Classical feedback for quantum channels, quant-ph/0409207v3.
Only the whole-codeword Markov assertion (PDF p.6) is stated. The six other
planned results are deferred in HARD.md because of source defects.
All definitions below are local to this paper. No product-input restriction is imposed.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P44

open scoped Matrix ComplexConjugate
open Filter

/-- PDF p.3: probability of a block whose per-letter surprisal differs from h by more
than e. Zero-mass words are excluded before their surprisal is used. The k=0 value is
irrelevant to convergence at infinity. Logarithms are base two. -/
def aepBadMass {S : Type*} [Fintype S]
    (p : (k : ℕ) → (Fin k → S) → ℝ) (h e : ℝ) (k : ℕ) : ℝ := by
  classical
  exact ∑ w : Fin k → S,
    if 0 < p k w ∧ e < |-(Real.logb 2 (p k w)) / (k : ℝ) - h|
    then p k w else 0

/-- PDF p.3: consistent normalized finite-alphabet block laws satisfying the AEP.
Consistency is marginalization of the last letter; the AEP is convergence in probability
of normalized base-two surprisal to the entropy rate. -/
structure FiniteAEPSource (S : Type*) [Fintype S] where
  probability : (k : ℕ) → (Fin k → S) → ℝ
  nonnegative : ∀ k w, 0 ≤ probability k w
  total : ∀ k, ∑ w, probability k w = 1
  consistent : ∀ k (w : Fin k → S),
    ∑ s, probability (k + 1) (Fin.snoc w s) = probability k w
  entropyRate : ℝ
  entropyRate_nonnegative : 0 ≤ entropyRate
  aep : ∀ e : ℝ, 0 < e →
    Tendsto (aepBadMass probability entropyRate e) atTop (nhds 0)

/-- PDF p.3: the empty source word has total probability one. -/
example {S : Type*} [Fintype S] (s : FiniteAEPSource S) :
    ∑ w : Fin 0 → S, s.probability 0 w = 1 := s.total 0

/-- PDF p.3: zero-mass words contribute no bad-event probability. -/
example {S : Type*} [Fintype S] (h e : ℝ) (k : ℕ) :
    aepBadMass (fun _ _ => 0 : (j : ℕ) → (Fin j → S) → ℝ) h e k = 0 := by
  simp [aepBadMass]

/-- PDF p.4: replace just the coordinates owned by a subsystem; every outside
coordinate is held fixed, including outside off-diagonal matrix entries. -/
def replaceSubsystem {n : ℕ} {H : Type*} (s : Fin n → Prop)
    [DecidablePred s] (x : Fin n → H) (z : {i // s i} → H) : Fin n → H :=
  fun i => if hi : s i then z ⟨i, hi⟩ else x i

/-- PDF p.4: an operation on exactly the indicated subsystem, identity on all
other factors. This is the full blockwise extension to entangled inputs. -/
def onSubsystem {n : ℕ} {H : Type*} (s : Fin n → Prop) [DecidablePred s]
    (f : Superop ({i // s i} → H) ({i // s i} → H)) :
    Superop (Fin n → H) (Fin n → H) :=
  fun X x y => f (fun z w => X (replaceSubsystem s x z) (replaceSubsystem s y w))
    (fun i => x i.val) (fun i => y i.val)

/-- PDF p.4: replacing subsystem coordinates by their existing values changes nothing. -/
example {n : ℕ} {H : Type*} (s : Fin n → Prop) [DecidablePred s]
    (x : Fin n → H) : replaceSubsystem s x (fun i => x i.val) = x := by
  funext i
  simp [replaceSubsystem]

/-- PDF p.4: lifting the identity keeps the entire matrix, including coherences. -/
example {n : ℕ} {H : Type*} (s : Fin n → Prop) [DecidablePred s]
    (X : Matrix (Fin n → H) (Fin n → H) ℂ) :
    onSubsystem s id X = X := by
  have hr (x : Fin n → H) : replaceSubsystem s x (fun i => x i.val) = x := by
    funext i
    simp [replaceSubsystem]
  funext x y
  change X (replaceSubsystem s x (fun i => x i.val))
    (replaceSubsystem s y (fun i => y i.val)) = X x y
  rw [hr x, hr y]

/-- PDF pp.2-4: fixed operations of an n-use feedback protocol on n designated input
factors. Receiver instruments act on factors already transmitted, sender responses
only on the strictly later factors. Outcomes use a common finite alphabet (unused
outcomes may have zero Kraus operator). The maps have no message/codeword argument.
The source decoder is deterministic postprocessing of the retained complete history;
it does not change the quantum execution and is not needed for this Markov result. -/
structure FeedbackProtocol (n : ℕ) (H K : Type*) [Fintype H] [DecidableEq H]
    [Fintype K] where
  channel : Superop H H
  channel_cptp : IsChannel channel
  instrument : (t : Fin n) → K →
    Matrix ({i : Fin n // i ≤ t} → H) ({i : Fin n // i ≤ t} → H) ℂ
  instrument_normalized : ∀ t, IsKrausFamily (instrument t)
  response : (t : Fin n) → K →
    Superop ({i : Fin n // t < i} → H) ({i : Fin n // t < i} → H)
  response_cptp : ∀ t k, IsChannel (response t k)

/-- PDF p.4: one physical forward call, receiver outcome k, and sender response.
At the last round the response acts on the empty tensor factor and is therefore
trivial. Kraus branches remain subnormalized; no conditional division is performed. -/
def FeedbackProtocol.step {n : ℕ} {H K : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] (C : FeedbackProtocol n H K) (t : Fin n) (k : K) :
    Superop (Fin n → H) (Fin n → H) :=
  fun X => onSubsystem (fun i => t < i) (C.response t k)
    (onSubsystem (fun i => i ≤ t) (conjSuperop (C.instrument t k))
      (piSuperop (fun i => if i = t then C.channel else id) X))

/-- PDF pp.4-5: execute all n rounds in order along history h, from the actual
possibly entangled codeword density matrix. The branch trace is its probability. -/
def FeedbackProtocol.branch {n : ℕ} {H K : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] (C : FeedbackProtocol n H K)
    (rho : Matrix (Fin n → H) (Fin n → H) ℂ) (h : Fin n → K) :
    Matrix (Fin n → H) (Fin n → H) ℂ :=
  (List.ofFn (fun t : Fin n => (t, h t))).foldl
    (fun X tk => C.step tk.1 tk.2 X) rho

/-- PDF p.4: no rounds means no channel call and the initial matrix is retained. -/
example {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]
    (C : FeedbackProtocol 0 H K) (rho : Matrix (Fin 0 → H) (Fin 0 → H) ℂ)
    (h : Fin 0 → K) : C.branch rho h = rho := by
  simp [FeedbackProtocol.branch]

/-- PDF p.4: a one-use execution is precisely its single channel/instrument/response step. -/
example {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]
    (C : FeedbackProtocol 1 H K) (rho : Matrix (Fin 1 → H) (Fin 1 → H) ℂ)
    (h : Fin 1 → K) : C.branch rho h = C.step 0 (h 0) rho := by
  simp [FeedbackProtocol.branch, List.ofFn_succ]

/-- PDF pp.4-6: terminal receiver state, including an orthogonal record of every
feedback outcome. All n physical systems have now been transmitted. Zero-probability
histories remain zero operator blocks, without normalized fallback states. -/
def FeedbackProtocol.receiver {n : ℕ} {H K : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (C : FeedbackProtocol n H K)
    (rho : Matrix (Fin n → H) (Fin n → H) ℂ) :
    Matrix ((Fin n → K) × (Fin n → H)) ((Fin n → K) × (Fin n → H)) ℂ :=
  fun u v => if u.1 = v.1 then C.branch rho u.1 u.2 v.2 else 0

/-- PDF p.5: diagonal history blocks are the executed unnormalized branch operators. -/
example {n : ℕ} {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]
    [DecidableEq K] (C : FeedbackProtocol n H K)
    (rho : Matrix (Fin n → H) (Fin n → H) ℂ) (h : Fin n → K) (x y : Fin n → H) :
    C.receiver rho (h, x) (h, y) = C.branch rho h x y := by
  simp [FeedbackProtocol.receiver]

/-- PDF pp.3-6: the derived joint state of message, full classical codeword, and
executed receiver. Registers are ordered M,(A,Z). Initially all physical factors
belong to the sender; no shared resource or extra quantum register is supplied. -/
def terminalState {n : ℕ} {S A H K : Type*} [Fintype S] [Fintype A]
    [DecidableEq A] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (src : FiniteAEPSource S) (c : (Fin n → S) → (Fin n → A))
    (rho : (Fin n → A) → Matrix (Fin n → H) (Fin n → H) ℂ)
    (C : FeedbackProtocol n H K) :
    Matrix ((Fin n → S) × ((Fin n → A) × ((Fin n → K) × (Fin n → H))))
      ((Fin n → S) × ((Fin n → A) × ((Fin n → K) × (Fin n → H)))) ℂ := by
  classical
  exact fun u v =>
    if u.1 = v.1 ∧ u.2.1 = c u.1 ∧ v.2.1 = c u.1 then
      (src.probability n u.1 : ℂ) * C.receiver (rho (c u.1)) u.2.2 v.2.2
    else 0

/-- PDF pp.5-6: fixing message and its full codeword exposes exactly the source
probability times the actually executed receiver block. -/
example {n : ℕ} {S A H K : Type*} [Fintype S] [Fintype A]
    [DecidableEq A] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (src : FiniteAEPSource S) (c : (Fin n → S) → (Fin n → A))
    (rho : (Fin n → A) → Matrix (Fin n → H) (Fin n → H) ℂ)
    (C : FeedbackProtocol n H K) (m : Fin n → S)
    (z w : (Fin n → K) × (Fin n → H)) :
    terminalState src c rho C (m, (c m, z)) (m, (c m, w)) =
      (src.probability n m : ℂ) * C.receiver (rho (c m)) z w := by
  classical
  simp [terminalState]

/-- PDF pp.5-6, with entropy convention p.2: I(M:Z|A) in bits from the four actual
marginal entropies S(MA)+S(AZ)-S(A)-S(MAZ), for register order M,(A,Z). -/
def conditionalInfo {M A Z : Type*} [Fintype M] [DecidableEq M] [Fintype A]
    [DecidableEq A] [Fintype Z] [DecidableEq Z]
    (X : Matrix (M × (A × Z)) (M × (A × Z)) ℂ) : ℝ :=
  vnEntropy (Matrix.of (fun p q : M × A => ∑ z : Z, X (p.1, (p.2, z)) (q.1, (q.2, z)))) +
    vnEntropy (traceLeft X) - vnEntropy (traceRight (traceLeft X)) - vnEntropy X

/-- PDF pp.2,6: the zero operator has zero conditional-information expression.
It is not admitted as a physical state by the theorem's density-matrix hypothesis. -/
example : conditionalInfo (0 : Matrix (Unit × (Unit × Unit)) (Unit × (Unit × Unit)) ℂ) = 0 := by
  simp only [conditionalInfo, traceLeft, traceRight, Matrix.of_apply,
    Matrix.zero_apply, Finset.sum_const_zero]
  change vnEntropy (0 : Matrix (Unit × Unit) (Unit × Unit) ℂ) +
    vnEntropy (0 : Matrix (Unit × Unit) (Unit × Unit) ℂ) -
    vnEntropy (0 : Matrix Unit Unit ℂ) -
    vnEntropy (0 : Matrix (Unit × (Unit × Unit)) (Unit × (Unit × Unit)) ℂ) = 0
  simp [vnEntropy]

end QAlgorithms.Papers.Independent.Next46.P44


