-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P31
-- name    : QAlgorithms_Papers_Independent_Claimed50_P31
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:23:12.128617+00:00
-- url     : https://prove2.me/theorems/21837423-0e76-430c-82f7-1623929f24f0
-- title:
--   Definitions for Composable Security in the Bounded-Quantum-Storage Model
-- statement:
--   The objects the formalized statements of *Composable Security in the Bounded-Quantum-Storage Model* (arXiv:0709.0492) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `eventProbability`: PDF p.5: the probability of an event in a discrete probability space. The ENNReal sum handles arbitrary discrete alphabets without an integrability default.
--   - `conditionalRetainedProbability`: PDF p.5: P[X=x,E | Y=y], where q(w)=P[w,E] is the retained subprobability mass and p is the original law. Unsupported conditioning values are zero; the denominator is not renormalized after deleting E.
--   - `EventEntropyThreshold`: PDF p.5: an entropy threshold achieved by deleting an event with probability at most epsilon. A submass q≤p represents P[w,E]; allowing all such submasses permits events on an extension of the probability space, not just events determined by (X,Y). This is event deletion, without renormalization.
--   - `eventSmoothMinEntropy`: PDF p.5: event-smoothed worst-case classical conditional min-entropy, in bits. Taking the supremum in EReal preserves +infinity if all mass can be deleted, and -infinity when no smoothing event is admissible.
--   - `bb84Vector`: PDF pp.4,6: BB84 encoding with false=computational and true=Hadamard. This is the tensor product of the indicated normalized one-qubit states.
--   - `BB84Measurement`: PDF p.6: a fixed measurement with arbitrary discrete outcome alphabet. The outcome laws are a bundled probability representation of the Born rule; the one effect family is independent of x and b. HasSum includes measurements with infinitely many classical outcomes. No quantum output is retained.
--   - `bb84Experiment`: PDF p.6: independently uniform X and B, followed by the same fixed measurement on |X>_B. The sample records (X,(B,K)).
--   - `splittingChoice`: PDF pp.10-11, Lemma 4.3: the prescribed choice bit. Its arguments include x1 and k but not the actual value of J. Conditional probabilities here use the original law, before event deletion.
--   - `splittingOutput`: PDF p.11: the joint variable (X_(1-C),C), with a tagged union when the two string alphabets differ. C is part of the variable, not the condition.
-- source:
--   Composable Security in the Bounded-Quantum-Storage Model, arXiv:0709.0492v1, https://arxiv.org/abs/0709.0492v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Information

/-!
Statements from Wehner and Wullschleger, arXiv:0709.0492v1.
The event-smoothed entropy below is the classical worst-case entropy of PDF p.5,
not a quantum conditional entropy or a purified-distance smoothing.
Protocol-security results needing a new execution semantics are deferred in HARD.md.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P31

open scoped ENNReal ComplexOrder

/-- PDF p.5: the probability of an event in a discrete probability space.
The ENNReal sum handles arbitrary discrete alphabets without an integrability default. -/
def eventProbability {Omega : Type*} (p : PMF Omega) (E : Set Omega) : ℝ≥0∞ := by
  classical
  exact ∑' w, if w ∈ E then p w else 0

/-- PDF p.5: P[X=x,E | Y=y], where q(w)=P[w,E] is the retained
subprobability mass and p is the original law. Unsupported conditioning values
are zero; the denominator is not renormalized after deleting E. -/
def conditionalRetainedProbability {Omega A B : Type*} (p : PMF Omega)
    (q : Omega → ℝ≥0∞) (X : Omega → A) (Y : Omega → B) (x : A) (y : B) : ℝ≥0∞ := by
  classical
  exact if eventProbability p {w | Y w = y} = 0 then 0 else
    (∑' w, if X w = x ∧ Y w = y then q w else 0) /
      eventProbability p {w | Y w = y}

/-- PDF p.5: an entropy threshold achieved by deleting an event with
probability at most epsilon. A submass q≤p represents P[w,E]; allowing all
such submasses permits events on an extension of the probability space, not
just events determined by (X,Y). This is event deletion, without renormalization. -/
def EventEntropyThreshold {Omega A B : Type*} (p : PMF Omega)
    (X : Omega → A) (Y : Omega → B) (epsilon h : ℝ) : Prop :=
  ∃ q : Omega → ℝ≥0∞, (∀ w, q w ≤ p w) ∧
    ENNReal.ofReal (1 - epsilon) ≤ ∑' w, q w ∧
    ∀ x y, conditionalRetainedProbability p q X Y x y ≤
      ENNReal.ofReal (Real.rpow 2 (-h))

/-- PDF p.5: event-smoothed worst-case classical conditional min-entropy,
in bits. Taking the supremum in EReal preserves +infinity if all mass can
be deleted, and -infinity when no smoothing event is admissible. -/
def eventSmoothMinEntropy {Omega A B : Type*} (p : PMF Omega)
    (X : Omega → A) (Y : Omega → B) (epsilon : ℝ) : EReal :=
  sSup {t : EReal | ∃ h : ℝ, t = (h : EReal) ∧ EventEntropyThreshold p X Y epsilon h}

/-- PDF pp.4,6: BB84 encoding with false=computational and true=Hadamard.
This is the tensor product of the indicated normalized one-qubit states. -/
def bb84Vector {n : ℕ} (x b : Qubits n) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun z => ∏ i : Fin n,
    if b i then hadamard (z i) (x i) else if z i = x i then 1 else 0

/-- PDF p.6: a fixed measurement with arbitrary discrete outcome alphabet.
The outcome laws are a bundled probability representation of the Born rule;
the one effect family is independent of x and b. HasSum includes measurements
with infinitely many classical outcomes. No quantum output is retained. -/
structure BB84Measurement (n : ℕ) (K : Type*) where
  effect : K → Matrix (Qubits n) (Qubits n) ℂ
  positive : ∀ k, (effect k).PosSemidef
  complete : HasSum effect 1
  law : Qubits n → Qubits n → PMF K
  born : ∀ x b k, law x b k = ENNReal.ofReal
    (effectProb (effect k) (pureDensity (bb84Vector x b)))

/-- PDF p.6: independently uniform X and B, followed by the same fixed
measurement on |X>_B. The sample records (X,(B,K)). -/
def bb84Experiment {n : ℕ} {K : Type*} (M : BB84Measurement n K) :
    PMF (Qubits n × (Qubits n × K)) :=
  (PMF.uniformOfFintype (Qubits n × Qubits n)).bind fun xb =>
    (M.law xb.1 xb.2).map fun k => (xb.1, (xb.2, k))

/-- PDF pp.10-11, Lemma 4.3: the prescribed choice bit. Its arguments
include x1 and k but not the actual value of J. Conditional probabilities here
use the original law, before event deletion. -/
def splittingChoice {Omega A1 K : Type*} (p : PMF Omega)
    (X1 : Omega → A1) (Kvar : Omega → K) {jCount : ℕ}
    (J : Omega → Fin jCount) (alpha beta : ℝ) (x1 : A1) (k : K) : Bool := by
  classical
  exact if ∃ j : Fin jCount,
    ENNReal.ofReal (Real.rpow 2 (-((alpha - beta) / 2))) ≤
      conditionalRetainedProbability p (fun w => p w) X1 (fun w => (Kvar w, J w)) x1 (k, j)
    then true else false

/-- PDF p.11: the joint variable (X_(1-C),C), with a tagged union when
the two string alphabets differ. C is part of the variable, not the condition. -/
def splittingOutput {Omega A0 A1 K : Type*} (p : PMF Omega)
    (X0 : Omega → A0) (X1 : Omega → A1) (Kvar : Omega → K) {jCount : ℕ}
    (J : Omega → Fin jCount) (alpha beta : ℝ) (w : Omega) : (Sum A0 A1) × Bool :=
  let c := splittingChoice p X1 Kvar J alpha beta (X1 w) (Kvar w)
  (if c then Sum.inl (X0 w) else Sum.inr (X1 w), c)

/-- The probability space is normalized and the empty event has zero mass. -/
example {Omega : Type*} (p : PMF Omega) :
    eventProbability p Set.univ = 1 ∧ eventProbability p ∅ = 0 := by
  classical
  simp [eventProbability, PMF.tsum_coe]

/-- Unsupported conditions contribute zero, rather than an undefined logarithm. -/
example {Omega A B : Type*} (p : PMF Omega) (q : Omega → ℝ≥0∞)
    (X : Omega → A) (Y : Omega → B) (x : A) (y : B)
    (hy : eventProbability p {w | Y w = y} = 0) :
    conditionalRetainedProbability p q X Y x y = 0 := by
  simp [conditionalRetainedProbability, hy]

/-- At epsilon=1 the entire event may be deleted, allowing every finite threshold. -/
example {Omega A B : Type*} (p : PMF Omega) (X : Omega → A) (Y : Omega → B) (h : ℝ) :
    EventEntropyThreshold p X Y 1 h := by
  classical
  refine ⟨fun _ => 0, fun _ => bot_le, by simp, ?_⟩
  intro x y
  simp [conditionalRetainedProbability]

/-- The zero-qubit tensor product is the one-dimensional unit amplitude. -/
example (x b z : Qubits 0) : bb84Vector x b z = 1 := by
  simp [bb84Vector]

/-- The |1> Hadamard-basis amplitude at |1> has the required minus sign. -/
example : bb84Vector (fun _ : Fin 1 => true) (fun _ => true) (fun _ => true) =
    -((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [bb84Vector, hadamard]

/-- A true computed choice selects X0 and keeps that choice in the joint variable. -/
example {Omega A0 A1 K : Type*} (p : PMF Omega)
    (X0 : Omega → A0) (X1 : Omega → A1) (Kvar : Omega → K) {jCount : ℕ}
    (J : Omega → Fin jCount) (alpha beta : ℝ) (w : Omega)
    (hc : splittingChoice p X1 Kvar J alpha beta (X1 w) (Kvar w) = true) :
    splittingOutput p X0 X1 Kvar J alpha beta w = (Sum.inl (X0 w), true) := by
  simp [splittingOutput, hc]

end QAlgorithms.Papers.Independent.Claimed50.P31


